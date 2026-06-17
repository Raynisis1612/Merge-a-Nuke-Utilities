-- ============================================================
--  Merge a Nuke Utilities  v1.4.0
--  Author: Claude
--  Game: Merge a Nuke (Place ID: 128784467030899)
-- ============================================================
--  GAME SOURCE NOTES:
--
--  1. PickUp remote → server validates → fires HoldStarted(tier) to client.
--  2. Drop remote  → server fires HoldEnded to client.
--  3. MergeRequest(targetPart) → server checks tier match + XZ dist ≤ 6 studs.
--  4. On merge success: server destroys both, creates tier+1, fires HoldStarted(tier+1).
--  5. Heartbeat scanner in NukeClient auto-picks up nukes within PICKUP_RADIUS (7 studs)
--     every PICKUP_SCAN_INTERVAL (0.1s) after DROP_DEBOUNCE (0.75s) since last drop.
--  6. RequestLockBase (no args) → locks your base. LockStateUpdate fires back with
--     phase ("free"|"locked"|"cooldown") and seconds remaining.
--
--  DROP-ZONE PROBLEM & FIX:
--  After dropping a nuke while standing on it, the Heartbeat scanner will re-pick it
--  up the instant DROP_DEBOUNCE elapses. Fix: immediately teleport DROP_ESCAPE_DIST
--  studs away, record the drop position, and don't target nukes near that zone.
--
--  TOO-CLOSE NUKE SEPARATION:
--  When two nukes of different tiers are ≤ CLOSE_NUKE_THRESHOLD studs apart, the
--  pickup scanner grabs whichever is nearest — which may be the wrong one. Fix:
--  pick up the obstructing nuke, walk SEPARATE_DIST studs away, drop it, then
--  approach the desired nuke from a safe direction.
-- ============================================================

local cloneref = (cloneref or clonereference or function(i) return i end)

local WindUI
do
    local ok, result = pcall(function() return require("./src/Init") end)
    if ok then
        WindUI = result
    else
        if cloneref(game:GetService("RunService")):IsStudio() then
            WindUI = require(cloneref(game:GetService("ReplicatedStorage")):WaitForChild("WindUI"):WaitForChild("Init"))
        else
            WindUI = loadstring(game:HttpGet("https://raw.githubusercontent.com/Footagesus/WindUI/main/dist/main.lua"))()
        end
    end
end

-- ──────────────────────────────────────────────────────────────
-- Services
-- ──────────────────────────────────────────────────────────────
local Players           = cloneref(game:GetService("Players"))
local TeleportService   = cloneref(game:GetService("TeleportService"))
local RunService        = cloneref(game:GetService("RunService"))
local ReplicatedStorage = cloneref(game:GetService("ReplicatedStorage"))
local Workspace         = cloneref(game:GetService("Workspace"))

local LocalPlayer = Players.LocalPlayer

-- ──────────────────────────────────────────────────────────────
-- Remotes
-- ──────────────────────────────────────────────────────────────
local NukeRemotes      = ReplicatedStorage:WaitForChild("NukeRemotes", 10)
local R_PickUp         = NukeRemotes and NukeRemotes:WaitForChild("PickUp",          5)
local R_Drop           = NukeRemotes and NukeRemotes:WaitForChild("Drop",            5)
local R_MergeRequest   = NukeRemotes and NukeRemotes:WaitForChild("MergeRequest",    5)
local R_HoldStarted    = NukeRemotes and NukeRemotes:WaitForChild("HoldStarted",     5)
local R_HoldEnded      = NukeRemotes and NukeRemotes:WaitForChild("HoldEnded",       5)
local R_RequestLock    = NukeRemotes and NukeRemotes:WaitForChild("RequestLockBase", 5)
local R_LockStateUpdate= NukeRemotes and NukeRemotes:WaitForChild("LockStateUpdate", 5)
local R_PurchaseUpgrade = NukeRemotes and NukeRemotes:WaitForChild("PurchaseUpgrade", 5)
local R_Rebirth         = NukeRemotes and NukeRemotes:WaitForChild("Rebirth", 5)

-- ──────────────────────────────────────────────────────────────
-- Game Config (from source)
-- ──────────────────────────────────────────────────────────────
local MERGE_RADIUS        = 6       -- XZ studs server checks for merge
local DROP_DEBOUNCE       = 0.75    -- server-side cooldown after drop
local PICKUP_RADIUS       = 7       -- auto-pickup range in NukeClient

-- Script-side tuning
local DROP_ESCAPE_DIST    = 15      -- studs to flee after dropping
local DROP_ZONE_RADIUS    = 10      -- radius to avoid around a recent drop
local DROP_ZONE_EXPIRE    = 4       -- seconds before a drop zone is forgotten
local CLOSE_NUKE_THRESHOLD = 4      -- studs: nukes closer than this need separation
local SEPARATE_DIST       = 18      -- studs to carry an obstructing nuke away

-- ──────────────────────────────────────────────────────────────
-- Held-tier tracking (authoritative — from server events)
-- ──────────────────────────────────────────────────────────────
local serverHeldTier = nil
local holdStartedConn, holdEndedConn

-- Drop-zone memory
local recentDrops = {}

holdStartedConn = R_HoldStarted and R_HoldStarted.OnClientEvent:Connect(function(tier)
    serverHeldTier = tier
end)

holdEndedConn = R_HoldEnded and R_HoldEnded.OnClientEvent:Connect(function()
    serverHeldTier = nil
end)

-- Lock-base state tracking
local lockPhase       = "free"   -- "free" | "locked" | "cooldown"
local lockSecondsLeft = 0

if R_LockStateUpdate then
    R_LockStateUpdate.OnClientEvent:Connect(function(phase, secs)
        lockPhase       = phase or "free"
        lockSecondsLeft = secs  or 0
    end)
end

-- ──────────────────────────────────────────────────────────────
-- State
-- ──────────────────────────────────────────────────────────────
local State = {
    autoMergeEnabled = false,
    autoMergeThread  = nil,
    autoMergeDelay   = 0.2,
    stats            = { merges = 0, drops = 0, errors = 0 },
    highestTier      = 0,

    autoLockEnabled  = false,
    autoLockThread   = nil,

    autoLeaveEnabled  = false,
    autoLeaveThread   = nil,
    rejoinDelay       = 0,     -- seconds before rejoining (default instant)
    detectionRadius   = 90,    -- studs from island center to detect incoming nukes

    smartLockEnabled  = false,
    smartLockThread   = nil,
    smartLockRadius   = 90,    -- studs from island center to activate smart lock

    autoRebirthEnabled = false,
    autoRebirthThread  = nil,

    autoRejoinEnabled = false,  -- periodic rejoin to prevent lag/perf issues
    autoRejoinThread  = nil,
    autoRejoinMinutes = 20,     -- minutes between periodic rejoins

    antiAfkEnabled   = false,
    antiAfkThread    = nil,

    autoUpgrade = {
        TIER     = false,
        MAX      = false,
        LOCKBASE = false,
    },
    autoUpgradeThreads = {},

    walkSpeed  = 16,
    jumpPower  = 50,
}

-- ──────────────────────────────────────────────────────────────
-- Basic helpers
-- ──────────────────────────────────────────────────────────────
local function getChar()      return LocalPlayer.Character end
local function getHRP()
    local c = getChar(); return c and c:FindFirstChild("HumanoidRootPart")
end
local function getHumanoid()
    local c = getChar(); return c and c:FindFirstChildWhichIsA("Humanoid")
end

local cachedNukesFolder = nil
local function getMyNukesFolder()
    if cachedNukesFolder and cachedNukesFolder.Parent then return cachedNukesFolder end
    cachedNukesFolder = nil
    local bases = Workspace:FindFirstChild("Bases")
    if not bases then return nil end
    for _, base in ipairs(bases:GetChildren()) do
        local nukes = base:FindFirstChild("Nukes")
        if nukes then
            for _, nuke in ipairs(nukes:GetChildren()) do
                if nuke:IsA("BasePart") and nuke:GetAttribute("OwnerUserId") == LocalPlayer.UserId then
                    cachedNukesFolder = nukes
                    return nukes
                end
            end
        end
    end
    return nil
end

local function xzDist(a, b)
    local dx = a.X - b.X
    local dz = a.Z - b.Z
    return math.sqrt(dx*dx + dz*dz)
end

local function teleportTo(pos)
    local hrp = getHRP()
    if not hrp then return end
    hrp.CFrame = CFrame.new(pos + Vector3.new(0, 4, 2))
end

local function getIslandCenter()
    local folder = getMyNukesFolder()
    if not folder then return Vector3.new(0, 0, 0) end
    local sum, count = Vector3.new(0,0,0), 0
    for _, part in ipairs(folder:GetChildren()) do
        if part:IsA("BasePart") and part:GetAttribute("OwnerUserId") == LocalPlayer.UserId then
            sum += part.Position; count += 1
        end
    end
    return count > 0 and (sum / count) or Vector3.new(0, 0, 0)
end

-- ──────────────────────────────────────────────────────────────
-- Drop-zone helpers
-- ──────────────────────────────────────────────────────────────
local function purgeOldDrops()
    local now = tick()
    for i = #recentDrops, 1, -1 do
        if now - recentDrops[i].time > DROP_ZONE_EXPIRE then
            table.remove(recentDrops, i)
        end
    end
end

local function recordDrop(tier)
    local hrp = getHRP(); if not hrp then return end
    purgeOldDrops()
    table.insert(recentDrops, { pos = hrp.Position, tier = tier, time = tick() })
end

-- Returns true if worldPos is within DROP_ZONE_RADIUS of a drop of a DIFFERENT tier.
-- Same-tier drops are fine — those are where we'll go to pick up.
local function nearRecentDrop(worldPos, ignoreTier)
    purgeOldDrops()
    for _, e in ipairs(recentDrops) do
        if e.tier ~= ignoreTier then
            if xzDist(worldPos, e.pos) < DROP_ZONE_RADIUS then
                return true
            end
        end
    end
    return false
end

-- After dropping, teleport DROP_ESCAPE_DIST studs away so the Heartbeat
-- scanner cannot re-grab the nuke before DROP_DEBOUNCE expires.
-- If nextTarget is already far enough, skip the extra teleport.
local function fleeDropZone(droppedPos, nextTargetPos)
    local hrp = getHRP(); if not hrp then return end

    if nextTargetPos and xzDist(nextTargetPos, droppedPos) >= DROP_ZONE_RADIUS then
        return  -- destination already safe, no escape needed
    end

    local myPos = hrp.Position
    local dx = myPos.X - droppedPos.X
    local dz = myPos.Z - droppedPos.Z
    local len = math.sqrt(dx*dx + dz*dz)
    if len < 0.1 then dx, dz, len = 1, 0, 1 end
    dx, dz = dx/len, dz/len

    teleportTo(Vector3.new(
        droppedPos.X + dx * DROP_ESCAPE_DIST,
        droppedPos.Y,
        droppedPos.Z + dz * DROP_ESCAPE_DIST
    ))
    task.wait(DROP_DEBOUNCE + 0.15)
end

-- ──────────────────────────────────────────────────────────────
-- Nuke scan (deprioritises nukes near foreign drop zones)
-- ──────────────────────────────────────────────────────────────
local function getMyNukesByTier()
    local folder = getMyNukesFolder()
    if not folder then return {} end
    purgeOldDrops()
    local byTier = {}
    for _, part in ipairs(folder:GetChildren()) do
        if part:IsA("BasePart") and part:GetAttribute("OwnerUserId") == LocalPlayer.UserId then
            local tier  = part:GetAttribute("Tier")
            local state = part:GetAttribute("State")
            if tier and (state == "floor" or state == "based" or state == nil) then
                if not byTier[tier] then byTier[tier] = {} end
                if nearRecentDrop(part.Position, tier) then
                    table.insert(byTier[tier], part)       -- deprioritise
                else
                    table.insert(byTier[tier], 1, part)    -- prefer safe nukes
                end
            end
        end
    end
    return byTier
end

-- ──────────────────────────────────────────────────────────────
-- Nuke separation
-- When nukeA and nukeB are ≤ CLOSE_NUKE_THRESHOLD studs apart and we
-- need to pick up nukeA specifically, first carry nukeB away then come back.
-- ──────────────────────────────────────────────────────────────
local function separateNuke(nukeToMove, referencePos)
    -- nukeToMove is the one we DON'T want; referencePos is where we'll return
    if serverHeldTier ~= nil then return end  -- already holding something, skip
    if not nukeToMove or not nukeToMove.Parent then return end

    -- Stand on the nuke we want to move
    teleportTo(nukeToMove.Position)
    task.wait(0.15)

    -- Pick it up
    pcall(function() R_PickUp:FireServer(nukeToMove) end)
    local t = tick()
    repeat task.wait(0.05) until serverHeldTier ~= nil or (tick()-t) > 1.5
    if serverHeldTier == nil then return end  -- couldn't pick up, give up

    -- Walk SEPARATE_DIST studs away from the reference nuke
    local hrp = getHRP()
    if not hrp then
        pcall(function() R_Drop:FireServer() end)
        serverHeldTier = nil
        return
    end

    local awayX = hrp.Position.X - referencePos.X
    local awayZ = hrp.Position.Z - referencePos.Z
    local awayLen = math.sqrt(awayX*awayX + awayZ*awayZ)
    if awayLen < 0.1 then awayX, awayZ, awayLen = 1, 0, 1 end
    awayX, awayZ = awayX/awayLen, awayZ/awayLen

    local dropPos = Vector3.new(
        referencePos.X + awayX * SEPARATE_DIST,
        referencePos.Y,
        referencePos.Z + awayZ * SEPARATE_DIST
    )
    teleportTo(dropPos)
    task.wait(0.1)

    -- Drop there
    local droppedTier = serverHeldTier
    local hrp2 = getHRP()
    local actualDrop = hrp2 and hrp2.Position or dropPos
    pcall(function() R_Drop:FireServer() end)
    local t2 = tick()
    repeat task.wait(0.05) until serverHeldTier == nil or (tick()-t2) > (DROP_DEBOUNCE + 0.5)
    serverHeldTier = nil
    State.stats.drops += 1
    if droppedTier then
        table.insert(recentDrops, { pos = actualDrop, tier = droppedTier, time = tick() })
    end

    -- Wait out the debounce fully before we do anything else
    task.wait(DROP_DEBOUNCE + 0.2)
end

-- ──────────────────────────────────────────────────────────────
-- Drop (unconditional) + flee
-- ──────────────────────────────────────────────────────────────
local function doDrop(nextTargetPos)
    local droppedTier = serverHeldTier
    local hrp         = getHRP()
    local droppedPos  = hrp and hrp.Position or Vector3.new(0, 0, 0)

    pcall(function() R_Drop:FireServer() end)
    State.stats.drops += 1
    local t = tick()
    repeat task.wait(0.05) until serverHeldTier == nil or (tick()-t) > (DROP_DEBOUNCE + 0.5)
    serverHeldTier = nil

    if droppedTier then
        recordDrop(droppedTier)
    end
    fleeDropZone(droppedPos, nextTargetPos)
end

-- ──────────────────────────────────────────────────────────────
-- Pick up — waits for HoldStarted confirmation
-- ──────────────────────────────────────────────────────────────
local function doPickUp(nuke)
    if not nuke or not nuke.Parent then return nil end
    local expectedTier = nuke:GetAttribute("Tier")
    if not expectedTier then return nil end
    if serverHeldTier ~= nil then
        warn("[MergeUtils] doPickUp called while already holding tier", serverHeldTier)
        return nil
    end

    -- If another nuke of a different tier is very close to this one, move it away first
    local folder = getMyNukesFolder()
    if folder then
        for _, other in ipairs(folder:GetChildren()) do
            if other ~= nuke and other:IsA("BasePart")
                and other:GetAttribute("OwnerUserId") == LocalPlayer.UserId then
                local otherTier  = other:GetAttribute("Tier")
                local otherState = other:GetAttribute("State")
                if otherTier and otherTier ~= expectedTier
                    and (otherState == "floor" or otherState == "based" or otherState == nil)
                    and xzDist(nuke.Position, other.Position) <= CLOSE_NUKE_THRESHOLD then
                    -- Move 'other' away so we can pick up 'nuke' cleanly
                    separateNuke(other, nuke.Position)
                    task.wait(0.1)
                    break  -- one separation per pickup attempt is enough
                end
            end
        end
    end

    -- Now actually pick up the target nuke
    if serverHeldTier ~= nil then
        -- separateNuke accidentally left us holding something — drop it
        doDrop(nuke.Position)
    end

    -- Re-teleport to nuke in case separation moved us
    teleportTo(nuke.Position)
    task.wait(0.15)

    if not nuke.Parent then return nil end
    pcall(function() R_PickUp:FireServer(nuke) end)
    local t = tick()
    repeat task.wait(0.05) until serverHeldTier ~= nil or (tick()-t) > 1.5

    if serverHeldTier == nil then
        warn("[MergeUtils] PickUp timed out")
        State.stats.errors += 1
        return nil
    end
    return serverHeldTier
end

-- ──────────────────────────────────────────────────────────────
-- Merge held nuke into target
-- ──────────────────────────────────────────────────────────────
local function doMergeInto(target, heldTier)
    if not target or not target.Parent then return false end
    local targetTier = target:GetAttribute("Tier")
    if targetTier ~= heldTier then
        warn("[MergeUtils] Tier mismatch: holding", heldTier, "target has", targetTier)
        return false
    end

    teleportTo(target.Position)
    task.wait(0.1)
    if not target.Parent then return false end

    local preMergeTier = serverHeldTier
    local ok = pcall(function() R_MergeRequest:FireServer(target) end)
    if not ok then State.stats.errors += 1; return false end

    local t = tick()
    repeat task.wait(0.05) until serverHeldTier ~= preMergeTier or (tick()-t) > 1.2

    if serverHeldTier == preMergeTier then
        warn("[MergeUtils] Merge rejected by server")
        State.stats.errors += 1
        return false
    end

    State.stats.merges += 1
    if serverHeldTier and serverHeldTier > State.highestTier then
        State.highestTier = serverHeldTier
    end
    return true, serverHeldTier
end

-- ──────────────────────────────────────────────────────────────
-- Main merge cycle
-- ──────────────────────────────────────────────────────────────
local function doMergeCycle()
    -- ── Phase A: already holding something ───────────────────
    if serverHeldTier ~= nil then
        local heldTier = serverHeldTier
        local byTier   = getMyNukesByTier()
        local targets  = byTier[heldTier]
        if targets and #targets >= 1 then
            local merged = doMergeInto(targets[1], heldTier)
            if merged then
                task.wait(0.3)
            else
                doDrop(getIslandCenter()); task.wait(0.3); return
            end
        else
            doDrop(getIslandCenter()); task.wait(0.3); return
        end
    end

    -- ── Phase B: check result tier for a chain merge ─────────
    if serverHeldTier ~= nil then
        local heldTier = serverHeldTier
        local byTier   = getMyNukesByTier()
        local targets  = byTier[heldTier]
        if targets and #targets >= 1 then
            local merged = doMergeInto(targets[1], heldTier)
            if merged then
                task.wait(0.3); return
            else
                doDrop(getIslandCenter()); task.wait(0.3); return
            end
        else
            doDrop(getIslandCenter()); task.wait(DROP_DEBOUNCE); return
        end
    end

    -- ── Phase C: find a new pair ──────────────────────────────
    local byTier = getMyNukesByTier()
    local mergeableTiers = {}
    for tier, nukes in pairs(byTier) do
        if #nukes >= 2 then table.insert(mergeableTiers, tier) end
    end
    table.sort(mergeableTiers)

    if #mergeableTiers == 0 then
        -- No pairs available — stand still and wait, do NOT teleport
        task.wait(1.5)
        return
    end

    local targetTier = mergeableTiers[1]
    local nukes      = byTier[targetTier]
    local nukeA      = nukes[1]
    local nukeB      = nukes[2]

    if not nukeA or not nukeA.Parent or not nukeB or not nukeB.Parent then return end
    if nukeA:GetAttribute("Tier") ~= targetTier then return end
    if nukeB:GetAttribute("Tier") ~= targetTier then return end

    -- If we're holding a nuke, check if its value is worth keeping or we should drop first
    -- IMPORTANT: always drop before teleporting to a small pair so we don't accidentally
    -- carry a high-value nuke to the wrong location.
    if serverHeldTier ~= nil then
        local heldNow = serverHeldTier
        -- If we're holding the same tier we want to merge, fast-path directly into it
        if heldNow == targetTier then
            local merged = doMergeInto(nukeA, heldNow)
            if merged then
                task.wait(0.3)
            else
                doDrop(getIslandCenter()); task.wait(0.3)
            end
            return
        end
        -- We're holding a different (likely higher) tier nuke — drop it safely first
        doDrop(getIslandCenter())
        task.wait(DROP_DEBOUNCE + 0.1)
        -- Re-scan after dropping since nukes may have changed
        return
    end

    -- Pick up nukeA (separation handled inside doPickUp)
    local heldTier = doPickUp(nukeA)
    if not heldTier then task.wait(0.5); return end

    if heldTier ~= targetTier then task.wait(0.2); return end

    task.wait(0.1)
    if not nukeB or not nukeB.Parent or nukeB:GetAttribute("Tier") ~= targetTier then
        doDrop(getIslandCenter()); task.wait(0.3); return
    end

    local merged = doMergeInto(nukeB, heldTier)
    if not merged then
        doDrop(getIslandCenter()); task.wait(0.3)
    else
        task.wait(0.2)
    end
end

-- ──────────────────────────────────────────────────────────────
-- Auto merge loop
-- ──────────────────────────────────────────────────────────────
local function autoMergeLoop()
    while State.autoMergeEnabled do
        local ok, err = pcall(doMergeCycle)
        if not ok then
            warn("[MergeUtils] Cycle crashed:", err)
            State.stats.errors += 1
            local hrp2 = getHRP()
            local crashPos = hrp2 and hrp2.Position or Vector3.new(0,0,0)
            if serverHeldTier then recordDrop(serverHeldTier) end
            pcall(function() R_Drop:FireServer() end)
            serverHeldTier = nil
            pcall(function() fleeDropZone(crashPos, getIslandCenter()) end)
        end
        task.wait(State.autoMergeDelay)
    end
    pcall(function() R_Drop:FireServer() end)
    serverHeldTier = nil
    table.clear(recentDrops)
end

local function startAutoMerge()
    if State.autoMergeThread then task.cancel(State.autoMergeThread) end
    pcall(function() R_Drop:FireServer() end)
    task.wait(DROP_DEBOUNCE + 0.2)
    serverHeldTier = nil
    table.clear(recentDrops)
    State.autoMergeEnabled = true
    State.autoMergeThread  = task.spawn(autoMergeLoop)
end

local function stopAutoMerge()
    State.autoMergeEnabled = false
    if State.autoMergeThread then task.cancel(State.autoMergeThread); State.autoMergeThread = nil end
    pcall(function() R_Drop:FireServer() end)
    serverHeldTier = nil
end

-- ──────────────────────────────────────────────────────────────
-- Auto-lock loop
-- Fires RequestLockBase only when the base is "free" (not already locked
-- and not on cooldown), then waits until it's locked before looping.
-- ──────────────────────────────────────────────────────────────
local function autoLockLoop()
    -- Track when we entered the current phase locally so that external phase
    -- changes (e.g. lock cancelled by launching a nuke) are noticed even while
    -- we are sleeping, rather than relying on a single fixed task.wait().
    local phaseEnteredAt = tick()
    local trackedPhase   = lockPhase

    while State.autoLockEnabled do
        -- Detect server-pushed phase change and reset local timer
        if lockPhase ~= trackedPhase then
            trackedPhase   = lockPhase
            phaseEnteredAt = tick()
        end

        if lockPhase == "free" then
            -- Immediately request a lock and wait up to 3 s for confirmation
            pcall(function() R_RequestLock:FireServer() end)
            local t = tick()
            repeat task.wait(0.2) until lockPhase ~= "free" or (tick() - t) > 3
        elseif lockPhase == "locked" then
            -- Poll every second; once our local elapsed time exceeds the
            -- server-reported remaining time, poke the server for an update
            -- (handles the case where the lock expired with no follow-up event).
            task.wait(1)
            local elapsed = tick() - phaseEnteredAt
            if elapsed >= math.max(lockSecondsLeft, 1) + 1 then
                pcall(function() R_RequestLock:FireServer() end)
                task.wait(0.5)
            end
        elseif lockPhase == "cooldown" then
            -- Poll every second; once elapsed ≥ cooldown time, attempt to lock.
            -- This handles nukes launched mid-lock that start an "unnatural"
            -- 30-second cooldown — we no longer miss the free window after it.
            task.wait(1)
            local elapsed = tick() - phaseEnteredAt
            if elapsed >= math.max(lockSecondsLeft, 1) + 0.5 then
                pcall(function() R_RequestLock:FireServer() end)
                local t = tick()
                repeat task.wait(0.2) until lockPhase ~= "cooldown" or (tick() - t) > 3
            end
        else
            task.wait(2)
        end
    end
end

local function startAutoLock()
    if State.autoLockThread then task.cancel(State.autoLockThread) end
    State.autoLockEnabled = true
    State.autoLockThread  = task.spawn(autoLockLoop)
end

local function stopAutoLock()
    State.autoLockEnabled = false
    if State.autoLockThread then task.cancel(State.autoLockThread); State.autoLockThread = nil end
end

-- ──────────────────────────────────────────────────────────────
-- Auto-upgrade: fires PurchaseUpgrade every interval regardless of cash
-- ──────────────────────────────────────────────────────────────
local UPGRADE_INTERVAL = 0.5  -- seconds between purchase attempts

local function startAutoUpgrade(key)
    if State.autoUpgradeThreads[key] then
        task.cancel(State.autoUpgradeThreads[key])
    end
    State.autoUpgrade[key] = true
    State.autoUpgradeThreads[key] = task.spawn(function()
        while State.autoUpgrade[key] do
            pcall(function() R_PurchaseUpgrade:FireServer(key) end)
            task.wait(UPGRADE_INTERVAL)
        end
    end)
end

local function stopAutoUpgrade(key)
    State.autoUpgrade[key] = false
    if State.autoUpgradeThreads[key] then
        task.cancel(State.autoUpgradeThreads[key])
        State.autoUpgradeThreads[key] = nil
    end
end

local function stopAllAutoUpgrades()
    for _, key in ipairs({"TIER", "MAX", "LOCKBASE"}) do
        stopAutoUpgrade(key)
    end
end


-- ──────────────────────────────────────────────────────────────
-- Auto Leave
-- Scans Workspace every 0.5s for BaseParts with State="flying"
-- launched by someone other than us, heading toward our island.
-- If detected while our base is NOT locked, teleports us out.
-- ──────────────────────────────────────────────────────────────
local LEAVE_SCAN_INTERVAL = 0.5
-- LEAVE_DETECT_RADIUS is now dynamic: read from State.detectionRadius (slider-controlled, default 90 studs)
-- REJOIN_DELAY is now dynamic: read from State.rejoinDelay (slider-controlled, default 0.1s)
-- Set SCRIPT_URL to your raw script URL (e.g. a Pastebin raw link) to auto re-execute after rejoin.
-- Leave as nil to skip auto re-execution.
local SCRIPT_URL          = "https://raw.githubusercontent.com/Raynisis1612/Merge-a-Nuke-Utilities/refs/heads/main/manu.lua"

local function getMyIslandFloor()
    local bases = Workspace:FindFirstChild("Bases")
    if not bases then return nil end
    for _, base in ipairs(bases:GetChildren()) do
        local nukes = base:FindFirstChild("Nukes")
        if nukes then
            for _, nuke in ipairs(nukes:GetChildren()) do
                if nuke:IsA("BasePart") and nuke:GetAttribute("OwnerUserId") == LocalPlayer.UserId then
                    return base:FindFirstChild("Floor")
                end
            end
        end
    end
    return nil
end

-- Resolve queue_on_teleport once at load time, exactly like Infinite Yield does:
-- direct variable access so executor-injected globals in getgenv() are found.
local queueteleport = queue_on_teleport
                   or (syn    and syn.queue_on_teleport)
                   or (fluxus and fluxus.queue_on_teleport)

print("[AutoLeave] queue_on_teleport resolved:", queueteleport ~= nil)

local function doRejoin()
    local rejoinDelay = State.rejoinDelay
    -- Countdown
    for i = math.ceil(rejoinDelay), 1, -1 do
        pcall(function()
            WindUI:Notify({
                Title    = "Auto Rejoin",
                Content  = "Rejoining in " .. i .. "s...",
                Icon     = "clock",
                Duration = 1.1,
            })
        end)
        task.wait(1)
    end

    -- Queue script re-execution before the teleport fires
    if SCRIPT_URL and SCRIPT_URL ~= "" then
        if queueteleport then
            local reexecCode = string.format(
                'loadstring(game:HttpGet(%q))()',
                SCRIPT_URL
            )
            local ok, err = pcall(queueteleport, reexecCode)
            if ok then
                print("[AutoLeave] Queued re-execution of:", SCRIPT_URL)
            else
                warn("[AutoLeave] queueteleport call failed:", err)
            end
        else
            warn("[AutoLeave] queue_on_teleport not found — script won't re-execute after rejoin. Check your executor supports it.")
        end
    end

    pcall(function()
        TeleportService:Teleport(game.PlaceId, LocalPlayer)
    end)
end

local function autoLeaveLoop()
    while State.autoLeaveEnabled do
        task.wait(LEAVE_SCAN_INTERVAL)
        pcall(function()
            -- Only act when base is NOT locked (cooldown or free = vulnerable)
            if lockPhase == "locked" then return end

            local floor = getMyIslandFloor()
            if not floor then return end
            local islandPos = floor.Position

            for _, obj in ipairs(Workspace:GetChildren()) do
                if obj:IsA("BasePart") or obj:IsA("Model") then
                    local state = obj:GetAttribute("State")
                    local launcher = obj:GetAttribute("LauncherUserId")
                    if state == "flying" and launcher and launcher ~= LocalPlayer.UserId then
                        local pos = obj:IsA("BasePart") and obj.Position or (obj:FindFirstChildWhichIsA("BasePart") and obj:FindFirstChildWhichIsA("BasePart").Position)
                        if pos then
                            local dx = pos.X - islandPos.X
                            local dz = pos.Z - islandPos.Z
                            if math.sqrt(dx*dx + dz*dz) <= State.detectionRadius then
                                State.autoLeaveEnabled = false
                                local rd = State.rejoinDelay
                                WindUI:Notify({ Title = "Auto Rejoin", Content = "Incoming nuke! Rejoining in " .. rd .. "s...", Duration = rd + 1 })
                                doRejoin()
                                return
                            end
                        end
                    end
                end
            end
        end)
    end
end

local function startAutoLeave()
    if State.autoLeaveThread then task.cancel(State.autoLeaveThread) end
    State.autoLeaveEnabled = true
    State.autoLeaveThread  = task.spawn(autoLeaveLoop)
end

local function stopAutoLeave()
    State.autoLeaveEnabled = false
    if State.autoLeaveThread then task.cancel(State.autoLeaveThread); State.autoLeaveThread = nil end
end

-- ──────────────────────────────────────────────────────────────
-- Periodic Auto Rejoin
-- Rejoins the game (and re-executes the script) after a set
-- number of minutes to prevent lag / performance degradation.
-- ──────────────────────────────────────────────────────────────
local function autoRejoinLoop()
    while State.autoRejoinEnabled do
        local waitSeconds = State.autoRejoinMinutes * 60
        -- Count down in 1-second ticks so the interval stays live
        local elapsed = 0
        while State.autoRejoinEnabled and elapsed < waitSeconds do
            task.wait(1)
            elapsed += 1
        end
        if not State.autoRejoinEnabled then break end

        State.autoRejoinEnabled = false
        WindUI:Notify({
            Title    = "Auto Rejoin",
            Content  = "Rejoining after " .. State.autoRejoinMinutes .. " min to refresh performance.",
            Icon     = "refresh-cw",
            Duration = 4,
        })
        task.wait(2)
        doRejoin()
    end
end

local function startAutoRejoin()
    if State.autoRejoinThread then task.cancel(State.autoRejoinThread) end
    State.autoRejoinEnabled = true
    State.autoRejoinThread  = task.spawn(autoRejoinLoop)
end

local function stopAutoRejoin()
    State.autoRejoinEnabled = false
    if State.autoRejoinThread then task.cancel(State.autoRejoinThread); State.autoRejoinThread = nil end
end

-- ──────────────────────────────────────────────────────────────
-- Anti-AFK
-- Prevents the Roblox AFK kick by hooking the LocalPlayer.Idled
-- event (fires ~20 min after last real input) and injecting a
-- virtual right-click to reset the idle counter.  A 15-minute
-- heartbeat loop provides a secondary fallback.
-- ──────────────────────────────────────────────────────────────
local VirtualUser  = game:GetService("VirtualUser")
local antiAfkConn  = nil   -- Idled event connection

local function antiAfkInput()
    pcall(function()
        local cam = workspace.CurrentCamera
        local cf  = cam and cam.CFrame or CFrame.new()
        VirtualUser:Button2Down(Vector2.zero, cf)
        task.wait(0.1)
        VirtualUser:Button2Up(Vector2.zero, cf)
    end)
end

local function startAntiAfk()
    if State.antiAfkThread then task.cancel(State.antiAfkThread) end
    if antiAfkConn then antiAfkConn:Disconnect(); antiAfkConn = nil end

    State.antiAfkEnabled = true

    -- Primary: trigger whenever Roblox raises the idle signal
    antiAfkConn = LocalPlayer.Idled:Connect(function()
        if State.antiAfkEnabled then antiAfkInput() end
    end)

    -- Secondary: proactive input every 15 minutes so the idle
    -- counter never reaches the 20-minute kick threshold
    State.antiAfkThread = task.spawn(function()
        while State.antiAfkEnabled do
            task.wait(15 * 60)
            if State.antiAfkEnabled then antiAfkInput() end
        end
    end)
end

local function stopAntiAfk()
    State.antiAfkEnabled = false
    if State.antiAfkThread then task.cancel(State.antiAfkThread); State.antiAfkThread = nil end
    if antiAfkConn then antiAfkConn:Disconnect(); antiAfkConn = nil end
end



-- ──────────────────────────────────────────────────────────────
-- Smart Lock
-- Monitors incoming enemy nukes within the detection radius and
-- fires RequestLockBase only when one is detected.
-- ──────────────────────────────────────────────────────────────
local SMART_LOCK_SCAN_INTERVAL = 0.3

local function smartLockLoop()
    while State.smartLockEnabled do
        task.wait(SMART_LOCK_SCAN_INTERVAL)
        pcall(function()
            if lockPhase == "locked" then return end -- already locked, nothing to do

            local floor = getMyIslandFloor()
            if not floor then return end
            local islandPos = floor.Position

            for _, obj in ipairs(Workspace:GetChildren()) do
                local state   = obj:GetAttribute("State")
                local launcher = obj:GetAttribute("LauncherUserId")
                if state == "flying" and launcher and launcher ~= LocalPlayer.UserId then
                    local pos
                    if obj:IsA("BasePart") then
                        pos = obj.Position
                    else
                        local bp = obj:FindFirstChildWhichIsA("BasePart")
                        pos = bp and bp.Position
                    end
                    if pos then
                        local dx = pos.X - islandPos.X
                        local dz = pos.Z - islandPos.Z
                        if math.sqrt(dx*dx + dz*dz) <= State.smartLockRadius then
                            -- Enemy nuke in range — request a lock immediately
                            pcall(function() R_RequestLock:FireServer() end)
                            task.wait(0.5) -- brief pause to let LockStateUpdate come back
                            break
                        end
                    end
                end
            end
        end)
    end
end

local function startSmartLock()
    if State.smartLockThread then task.cancel(State.smartLockThread) end
    State.smartLockEnabled = true
    State.smartLockThread  = task.spawn(smartLockLoop)
end

local function stopSmartLock()
    State.smartLockEnabled = false
    if State.smartLockThread then task.cancel(State.smartLockThread); State.smartLockThread = nil end
end

-- ──────────────────────────────────────────────────────────────
-- Auto Rebirth
-- Fires the Rebirth remote on an interval so the player auto-rebirths.
-- ──────────────────────────────────────────────────────────────
local REBIRTH_INTERVAL = 0.5

local function startAutoRebirth()
    if State.autoRebirthThread then task.cancel(State.autoRebirthThread) end
    State.autoRebirthEnabled = true
    State.autoRebirthThread = task.spawn(function()
        while State.autoRebirthEnabled do
            pcall(function() R_Rebirth:FireServer() end)
            task.wait(REBIRTH_INTERVAL)
        end
    end)
end

local function stopAutoRebirth()
    State.autoRebirthEnabled = false
    if State.autoRebirthThread then task.cancel(State.autoRebirthThread); State.autoRebirthThread = nil end
end

-- ──────────────────────────────────────────────────────────────
-- Fling on Touch (Walk Fling)
-- Uses velocity de-sync to fling any player your character touches.
-- Derived from DrGemini's fling technique.
-- ──────────────────────────────────────────────────────────────
local flingEnabled  = false
local flingConn     = nil

local function startFlingOnTouch()
    flingEnabled = true
    if flingConn then flingConn:Disconnect() end

    flingConn = RunService.Heartbeat:Connect(function()
        if not flingEnabled then return end
        local hrp = getHRP()
        if not hrp then return end

        -- Velocity spike on the local root causes fling on server collision
        local orig = hrp.Velocity
        hrp.Velocity = (orig * 10000) + Vector3.new(0, 10000, 0)
        RunService.RenderStepped:Wait()
        hrp.Velocity = orig
        RunService.Stepped:Wait()
        hrp.Velocity = orig + Vector3.new(0, 0.1, 0)
    end)
end

local function stopFlingOnTouch()
    flingEnabled = false
    if flingConn then flingConn:Disconnect(); flingConn = nil end
end

-- ──────────────────────────────────────────────────────────────
-- Tier helpers (display)
-- ──────────────────────────────────────────────────────────────
local function tierToValue(tier)
    if tier <= 52 then
        return tostring(math.floor(2 ^ (tier - 1)))
    else
        local exp = math.floor((tier - 1) * math.log10(2))
        local m   = math.floor((10 ^ ((tier - 1) * math.log10(2) - exp)) * 10) / 10
        return m .. "e+" .. exp
    end
end

-- ──────────────────────────────────────────────────────────────
-- Character stat updater
-- ──────────────────────────────────────────────────────────────
LocalPlayer.CharacterAdded:Connect(function(char)
    local hum = char:WaitForChild("Humanoid", 5)
    if hum then
        task.wait(0.5)
        hum.WalkSpeed = State.walkSpeed
        hum.JumpPower = State.jumpPower
    end
end)

-- ──────────────────────────────────────────────────────────────
-- UI
-- ──────────────────────────────────────────────────────────────
local Window = WindUI:CreateWindow({
    Title       = "Merge a Nuke Utilities",
    Icon        = "solar:atom-bold",
    Author      = "by Claude  •  v1.4.0",
    Folder      = "MergeANukeUtils",
    NewElements = true,
    Topbar      = { Height = 44, ButtonsType = "Mac" },
    OpenButton  = {
        Title        = "Nuke Hub",
        CornerRadius = UDim.new(1, 0),
        Enabled      = true,
        Draggable    = true,
        Scale        = 0.5,
        Color = ColorSequence.new(Color3.fromHex("#FF4500"), Color3.fromHex("#FF8C00")),
    },
})

Window:Tag({ Title = "v1.4.0", Icon = "zap", Color = Color3.fromHex("#1a1a2e"), Border = true })

-- ──────────────────────────────────────────────────────────────
-- Auto-save helper
-- Debounced: waits 1.5 s after the last change before writing.
-- Called inside every toggle/slider callback so "default" always
-- reflects the current session state before a rejoin fires.
-- ──────────────────────────────────────────────────────────────
local _autoSaveThread = nil
local function scheduleAutoSave()
    if _autoSaveThread then task.cancel(_autoSaveThread) end
    _autoSaveThread = task.delay(1.5, function()
        _autoSaveThread = nil
        pcall(function()
            Window.ConfigManager:Config("default"):Save()
        end)
    end)
end

-- ── MAIN SECTION ─────────────────────────────────────────────
local MainSection = Window:Section({ Title = "Main" })

-- ── Auto Merge Tab ───────────────────────────────────────────
local MergeTab = MainSection:Tab({
    Title = "Auto Merge", Icon = "git-merge",
    IconColor = Color3.fromHex("#FF4500"), Border = true,
})

do
    local autoSec = MergeTab:Section({ Title = "Auto Merger", Box = true, BoxBorder = true, Opened = true })
    autoSec:Toggle({
        Title = "Enable Auto Merge", Icon = "git-merge",
        Desc  = "Auto-merges nuke pairs.",
        Value = false, Flag = "autoMerge",
        Callback = function(state)
            scheduleAutoSave()
            if state then
                if not R_PickUp or not R_MergeRequest or not R_HoldStarted then
                    WindUI:Notify({ Title = "Error", Content = "Remotes not found. Make sure you're in game.", Icon = "alert-circle", Duration = 4 })
                    return
                end
                startAutoMerge()
                WindUI:Notify({ Title = "Auto Merge", Content = "Started!", Icon = "git-merge", Duration = 3 })
            else
                stopAutoMerge()
                WindUI:Notify({ Title = "Auto Merge", Content = "Stopped.", Duration = 2 })
            end
        end,
    })
    autoSec:Space()
    autoSec:Slider({
        Title = "Cycle Delay (s)",
        Desc  = "Delay between merge cycles.",
        Value = { Min = 0.2, Max = 3.0, Default = 0.2 }, Step = 0.1,
        IsTooltip = true, Flag = "mergeDelay",
        Callback = function(v) State.autoMergeDelay = v; scheduleAutoSave() end,
    })
    MergeTab:Space()

    local manualSec = MergeTab:Section({ Title = "Manual Controls", Box = true, BoxBorder = true, Opened = true })
    manualSec:Button({
        Title = "Force Drop",
        Desc  = "Drops held nuke and flees.",
        Icon  = "arrow-down", Justify = "Center",
        Color = Color3.fromHex("#EF4444"),
        Callback = function()
            task.spawn(function()
                doDrop(getIslandCenter())
                WindUI:Notify({ Title = "Drop", Content = "Dropped and fled drop zone.", Duration = 2 })
            end)
        end,
    })
    manualSec:Space()
    manualSec:Button({
        Title = "Merge Once",
        Desc  = "Run one merge cycle.",
        Icon  = "zap", Justify = "Center",
        Color = Color3.fromHex("#FF4500"),
        Callback = function()
            task.spawn(function()
                local ok, err = pcall(doMergeCycle)
                if not ok then
                    WindUI:Notify({ Title = "Merge Once", Content = "Error: " .. tostring(err), Icon = "alert-circle", Duration = 3 })
                else
                    WindUI:Notify({ Title = "Merge Once", Content = "Cycle done.", Icon = "check", Duration = 2 })
                end
            end)
        end,
    })
end

-- ── Auto Lock Tab ────────────────────────────────────────────
local LockTab = MainSection:Tab({
    Title = "Auto Lock", Icon = "shield",
    IconColor = Color3.fromHex("#34D399"), Border = true,
})
do
    local lockSec = LockTab:Section({ Title = "Auto Lock Base", Box = true, BoxBorder = true, Opened = true })

    local lockStatusPara = lockSec:Paragraph({
        Title = "Status",
        Desc  = "Phase: free",
    })

    lockSec:Space()

    lockSec:Toggle({
        Title = "Enable Auto Lock", Icon = "shield",
        Desc  = "Keeps your island locked at all times.",
        Value = false, Flag = "autoLock",
        Callback = function(state)
            scheduleAutoSave()
            if state then
                if not R_RequestLock then
                    WindUI:Notify({ Title = "Error", Content = "RequestLockBase remote not found.", Icon = "alert-circle", Duration = 4 })
                    return
                end
                startAutoLock()
                WindUI:Notify({ Title = "Auto Lock", Content = "Started!", Icon = "shield", Duration = 3 })
            else
                stopAutoLock()
                WindUI:Notify({ Title = "Auto Lock", Content = "Stopped.", Duration = 2 })
            end
        end,
    })

    lockSec:Space()

    lockSec:Toggle({
        Title = "Smart Lock", Icon = "shield-off",
        Desc  = "Locks only when an enemy nuke enters your detection radius.",
        Value = false, Flag = "smartLock",
        Callback = function(state)
            scheduleAutoSave()
            if state then
                if not R_RequestLock then
                    WindUI:Notify({ Title = "Error", Content = "RequestLockBase remote not found.", Icon = "alert-circle", Duration = 4 })
                    return
                end
                startSmartLock()
                WindUI:Notify({ Title = "Smart Lock", Content = "Active.", Icon = "shield-off", Duration = 3 })
            else
                stopSmartLock()
                WindUI:Notify({ Title = "Smart Lock", Content = "Stopped.", Duration = 2 })
            end
        end,
    })

    lockSec:Space()

    lockSec:Slider({
        Title = "Smart Lock Radius",
        Desc  = "Studs from your island to trigger a lock.",
        Value = { Min = 10, Max = 200, Default = 90 }, Step = 1,
        IsTooltip = true, IsTextbox = true, Flag = "smartLockRadius",
        Callback = function(v)
            State.smartLockRadius = v; scheduleAutoSave()
        end,
    })

    lockSec:Space()

    lockSec:Button({
        Title = "Lock Now", Icon = "shield", Justify = "Center",
        Color = Color3.fromHex("#34D399"),
        Desc  = "Send a lock request now.",
        Callback = function()
            pcall(function() R_RequestLock:FireServer() end)
            WindUI:Notify({ Title = "Lock", Content = "Lock request sent.", Duration = 2 })
        end,
    })

    -- Live lock-status updater
    task.spawn(function()
        while true do
            task.wait(1)
            pcall(function()
                local phaseStr = lockPhase
                local detail   = ""
                if lockPhase == "locked" then
                    detail = ("  (%02d:%02d remaining)"):format(
                        math.floor(lockSecondsLeft / 60), lockSecondsLeft % 60)
                elseif lockPhase == "cooldown" then
                    detail = ("  (%ds cooldown)"):format(lockSecondsLeft)
                end
                local autoStr = State.autoLockEnabled and "  [Auto: ON]" or (State.smartLockEnabled and "  [Smart: ON]" or "  [Auto: OFF]")
                lockStatusPara:setTitle("Status")
                lockStatusPara:setDesc("Phase: " .. phaseStr .. detail .. autoStr)
            end)
        end
    end)
end

-- ── Auto Upgrade Tab ────────────────────────────────────────
local UpgradeTab = MainSection:Tab({
    Title = "Auto Upgrade", Icon = "trending-up",
    IconColor = Color3.fromHex("#FBBF24"), Border = true,
})
do
    local upgSec = UpgradeTab:Section({ Title = "Upgrades", Box = true, BoxBorder = true, Opened = true })

    upgSec:Toggle({
        Title = "Spawn Tier", Desc = "Auto-buys Spawn Tier upgrades.",
        Value = false, Flag = "autoUpg_TIER",
        Callback = function(state)
            scheduleAutoSave()
            if state then startAutoUpgrade("TIER") else stopAutoUpgrade("TIER") end
        end,
    })
    upgSec:Space()

    upgSec:Toggle({
        Title = "Max Spawns", Desc = "Auto-buys Max Spawns upgrades.",
        Value = false, Flag = "autoUpg_MAX",
        Callback = function(state)
            scheduleAutoSave()
            if state then startAutoUpgrade("MAX") else stopAutoUpgrade("MAX") end
        end,
    })
    upgSec:Space()

    upgSec:Toggle({
        Title = "Lock Cooldown", Desc = "Auto-buys Lock Cooldown upgrades.",
        Value = false, Flag = "autoUpg_LOCKBASE",
        Callback = function(state)
            scheduleAutoSave()
            if state then startAutoUpgrade("LOCKBASE") else stopAutoUpgrade("LOCKBASE") end
        end,
    })
end

-- ── Auto Rebirth Tab ────────────────────────────────────────
local RebirthTab = MainSection:Tab({
    Title = "Auto Rebirth", Icon = "rotate-ccw",
    IconColor = Color3.fromHex("#FB923C"), Border = true,
})
do
    local rebirthSec = RebirthTab:Section({ Title = "Auto Rebirth", Box = true, BoxBorder = true, Opened = true })

    rebirthSec:Toggle({
        Title = "Enable Auto Rebirth", Icon = "rotate-ccw",
        Desc  = "Automatically rebirths for you.",
        Value = false, Flag = "autoRebirth",
        Callback = function(state)
            scheduleAutoSave()
            if state then
                startAutoRebirth()
                WindUI:Notify({ Title = "Auto Rebirth", Content = "Active.", Icon = "rotate-ccw", Duration = 3 })
            else
                stopAutoRebirth()
                WindUI:Notify({ Title = "Auto Rebirth", Content = "Stopped.", Duration = 2 })
            end
        end,
    })
end

-- ── Anti Nuke Tab ────────────────────────────────────────────
local LeaveTab = MainSection:Tab({
    Title = "Anti Nuke", Icon = "shield-x",
    IconColor = Color3.fromHex("#F87171"), Border = true,
})
do
    local leaveSec = LeaveTab:Section({ Title = "Anti Nuke", Box = true, BoxBorder = true, Opened = true })

    leaveSec:Toggle({
        Title = "Enable Anti Nuke", Icon = "shield-x",
        Desc  = "Leaves and rejoins when an enemy nuke enters your detection radius while unlocked.",
        Value = false, Flag = "autoLeave",
        Callback = function(state)
            scheduleAutoSave()
            if state then
                startAutoLeave()
                WindUI:Notify({ Title = "Anti Nuke", Content = "Active. Watching for incoming nukes.", Duration = 3 })
            else
                stopAutoLeave()
                WindUI:Notify({ Title = "Anti Nuke", Content = "Stopped.", Duration = 2 })
            end
        end,
    })

    leaveSec:Space()

    leaveSec:Slider({
        Title = "Rejoin Delay",
        Desc  = "Seconds to wait before rejoining after a nuke is detected. 0 = instant.",
        Value = { Min = 0, Max = 5, Default = 0 }, Step = 0.1,
        IsTooltip = true, IsTextbox = true, Flag = "rejoinDelay",
        Callback = function(v)
            State.rejoinDelay = v; scheduleAutoSave()
        end,
    })

    leaveSec:Space()

    leaveSec:Slider({
        Title = "Detection Radius",
        Desc  = "Studs from your island center to watch for incoming enemy nukes.",
        Value = { Min = 10, Max = 200, Default = 90 }, Step = 1,
        IsTooltip = true, IsTextbox = true, Flag = "detectionRadius",
        Callback = function(v)
            State.detectionRadius = v; scheduleAutoSave()
        end,
    })
end

-- ── Auto Rejoin Tab ──────────────────────────────────────────
local RejoinTab = MainSection:Tab({
    Title = "Auto Rejoin", Icon = "refresh-cw",
    IconColor = Color3.fromHex("#A78BFA"), Border = true,
})
do
    local rejoinSec = RejoinTab:Section({ Title = "Auto Rejoin", Box = true, BoxBorder = true, Opened = true })

    rejoinSec:Toggle({
        Title = "Auto Rejoin (Performance)",
        Icon  = "refresh-cw",
        Desc  = "Rejoins and re-executes the script on a timer to prevent lag.",
        Value = false, Flag = "autoRejoin",
        Callback = function(state)
            scheduleAutoSave()
            if state then
                startAutoRejoin()
                WindUI:Notify({ Title = "Auto Rejoin", Content = "Periodic rejoin active (" .. State.autoRejoinMinutes .. " min).", Duration = 3 })
            else
                stopAutoRejoin()
                WindUI:Notify({ Title = "Auto Rejoin", Content = "Periodic rejoin stopped.", Duration = 2 })
            end
        end,
    })

    rejoinSec:Space()

    rejoinSec:Slider({
        Title = "Rejoin Interval (Minutes)",
        Desc  = "Minutes between periodic rejoins.",
        Value = { Min = 5, Max = 60, Default = 20 }, Step = 1,
        IsTooltip = true, IsTextbox = true, Flag = "rejoinInterval",
        Callback = function(v)
            State.autoRejoinMinutes = v; scheduleAutoSave()
        end,
    })
end


-- ── Anti-AFK Tab ──────────────────────────────────────────────────────────────
local AntiAfkTab = MainSection:Tab({
    Title = "Anti-AFK", Icon = "activity",
    IconColor = Color3.fromHex("#60A5FA"), Border = true,
})
do
    local afkSec = AntiAfkTab:Section({ Title = "Anti-AFK", Box = true, BoxBorder = true, Opened = true })

    afkSec:Toggle({
        Title = "Enable Anti-AFK", Icon = "activity",
        Desc  = "Prevents AFK kicks by simulating input every 20 seconds.",
        Value = false, Flag = "antiAfk",
        Callback = function(state)
            scheduleAutoSave()
            if state then
                startAntiAfk()
                WindUI:Notify({ Title = "Anti-AFK", Content = "Active. AFK kick prevention enabled.", Duration = 3 })
            else
                stopAntiAfk()
                WindUI:Notify({ Title = "Anti-AFK", Content = "Stopped.", Duration = 2 })
            end
        end,
    })
end

-- ── PLAYER TAB ───────────────────────────────────────────────
local PlayerSection = Window:Section({ Title = "Player" })
local PlayerTab = PlayerSection:Tab({
    Title = "Character", Icon = "user",
    IconColor = Color3.fromHex("#34D399"), Border = true,
})
do
    local moveSec = PlayerTab:Section({ Title = "Movement", Box = true, BoxBorder = true, Opened = true })
    moveSec:Slider({
        Title = "Walk Speed", Desc = "Default 16.",
        Value = { Min = 16, Max = 100, Default = 50 }, Step = 1,
        IsTooltip = true, Flag = "walkSpeed",
        Callback = function(v)
            State.walkSpeed = v
            local hum = getHumanoid(); if hum then hum.WalkSpeed = v end
            scheduleAutoSave()
        end,
    })
    moveSec:Space()
    moveSec:Slider({
        Title = "Jump Power", Value = { Min = 10, Max = 200, Default = 50 }, Step = 5,
        IsTooltip = true, Flag = "jumpPower",
        Callback = function(v)
            State.jumpPower = v
            local hum = getHumanoid(); if hum then hum.JumpPower = v end
            scheduleAutoSave()
        end,
    })
    moveSec:Space()
    moveSec:Button({
        Title = "Reset Defaults", Icon = "rotate-ccw", Justify = "Center",
        Callback = function()
            State.walkSpeed = 16; State.jumpPower = 50
            local hum = getHumanoid()
            if hum then hum.WalkSpeed = 16; hum.JumpPower = 50 end
            WindUI:Notify({ Title = "Movement", Content = "Reset.", Duration = 2 })
        end,
    })
    PlayerTab:Space()

    local noClipSec = PlayerTab:Section({ Title = "No-Clip", Box = true, BoxBorder = true, Opened = true })
    local noClipConn = nil
    noClipSec:Toggle({
        Title = "No-Clip", Icon = "layers", Value = false, Flag = "noClip",
        Desc  = "Phase through walls.",
        Callback = function(state)
            if state then
                noClipConn = RunService.Stepped:Connect(function()
                    local char = getChar()
                    if char then
                        for _, p in ipairs(char:GetDescendants()) do
                            if p:IsA("BasePart") then p.CanCollide = false end
                        end
                    end
                end)
            else
                if noClipConn then noClipConn:Disconnect(); noClipConn = nil end
                local char = getChar()
                if char then
                    for _, p in ipairs(char:GetDescendants()) do
                        if p:IsA("BasePart") then p.CanCollide = true end
                    end
                end
            end
        end,
    })
end

-- ── FUN SECTION ──────────────────────────────────────────────
local FunSection = Window:Section({ Title = "Fun" })
local FunTab = FunSection:Tab({
    Title = "Fun", Icon = "zap",
    IconColor = Color3.fromHex("#A855F7"), Border = true,
})
do
    local iySec = FunTab:Section({ Title = "Infinite Yield", Box = true, BoxBorder = true, Opened = true })

    iySec:Button({
        Title    = "Execute Infinite Yield",
        Desc     = "Loads the Infinite Yield admin command script.",
        Icon     = "terminal",
        Justify  = "Center",
        Color    = Color3.fromHex("#A855F7"),
        Callback = function()
            task.spawn(function()
                loadstring(game:HttpGet("https://raw.githubusercontent.com/EdgeIY/infiniteyield/master/source"))()
            end)
            WindUI:Notify({ Title = "Infinite Yield", Content = "Loading...", Icon = "terminal", Duration = 3 })
        end,
    })

    FunTab:Space()

    -- ── Walk Fling ──────────────────────────────────────────
    local flingSec = FunTab:Section({ Title = "Walk Fling", Box = true, BoxBorder = true, Opened = true })

    flingSec:Toggle({
        Title = "Fling on Touch", Icon = "zap",
        Desc  = "Flings players your character touches.",
        Value = false, Flag = "flingOnTouch",
        Callback = function(state)
            if state then
                startFlingOnTouch()
                WindUI:Notify({ Title = "Walk Fling", Content = "Active.", Icon = "zap", Duration = 3 })
            else
                stopFlingOnTouch()
                WindUI:Notify({ Title = "Walk Fling", Content = "Stopped.", Duration = 2 })
            end
        end,
    })

    FunTab:Space()

    -- ── Teleport to Player ──────────────────────────────────
    local tpSec = FunTab:Section({ Title = "Teleport to Player", Box = true, BoxBorder = true, Opened = true })

    local playerDropdown
    playerDropdown = tpSec:Dropdown({
        Title     = "Select Player",
        Desc      = "Choose a player to teleport to.",
        Values    = {},
        AllowNone = true,
        Flag      = "tpPlayerSelect",
        Callback  = function(_) end,
    })

    tpSec:Space()

    -- Refresh player list on open and via button
    local function refreshPlayerList()
        local names = {}
        for _, p in ipairs(Players:GetPlayers()) do
            if p ~= LocalPlayer then
                table.insert(names, p.Name)
            end
        end
        pcall(function() playerDropdown:Refresh(names) end)
    end

    -- Auto-refresh when players join/leave
    Players.PlayerAdded:Connect(function() task.wait(0.5); refreshPlayerList() end)
    Players.PlayerRemoving:Connect(function() task.wait(0.5); refreshPlayerList() end)
    task.defer(refreshPlayerList)

    local tpStack = tpSec:HStack({ AutoSpace = true })

    tpStack:Button({
        Title = "Teleport", Icon = "user", Justify = "Center",
        Color = Color3.fromHex("#60A5FA"),
        Callback = function()
            local selected = playerDropdown.Value
            if not selected or selected == "" then
                WindUI:Notify({ Title = "Teleport", Content = "Select a player first.", Icon = "alert-circle", Duration = 3 })
                return
            end
            local target = Players:FindFirstChild(selected)
            if not target or not target.Character then
                WindUI:Notify({ Title = "Teleport", Content = "Player not found.", Icon = "alert-circle", Duration = 3 })
                return
            end
            local targetHRP = target.Character:FindFirstChild("HumanoidRootPart")
            if not targetHRP then
                WindUI:Notify({ Title = "Teleport", Content = "Target has no root.", Icon = "alert-circle", Duration = 3 })
                return
            end
            teleportTo(targetHRP.Position)
            WindUI:Notify({ Title = "Teleport", Content = "Teleported to " .. selected .. ".", Icon = "user", Duration = 2 })
        end,
    })

    tpStack:Button({
        Title = "Refresh", Icon = "refresh-cw", Justify = "Center",
        Callback = function()
            refreshPlayerList()
            WindUI:Notify({ Title = "Players", Content = "List refreshed.", Duration = 2 })
        end,
    })
end

-- ── SETTINGS TAB ─────────────────────────────────────────────
local SettingsSection = Window:Section({ Title = "Settings" })
local SettingsTab = SettingsSection:Tab({
    Title = "Settings", Icon = "settings",
    IconColor = Color3.fromHex("#94A3B8"), Border = true,
})
do
    local uiSec = SettingsTab:Section({ Title = "UI", Box = true, BoxBorder = true, Opened = true })
    uiSec:Keybind({
        Title = "Toggle Hub", Value = "V", Flag = "toggleKey",
        Callback = function(key) Window:SetToggleKey(Enum.KeyCode[key]) end,
    })
    uiSec:Space()
    uiSec:Slider({
        Title = "UI Scale", Value = { Min = 0.5, Max = 1.5, Default = 1.0 }, Step = 0.05,
        IsTooltip = true, Flag = "uiScale",
        Callback = function(v) Window:SetUIScale(v); scheduleAutoSave() end,
    })
    SettingsTab:Space()

    -- ── Config System ──────────────────────────────────────────
    local configSec = SettingsTab:Section({ Title = "Configs", Box = true, BoxBorder = true, Opened = true })

    local ConfigManager = Window.ConfigManager

    local configDropdown
    configDropdown = configSec:Dropdown({
        Title  = "Saved Configs",
        Desc   = "Select a config to load or delete.",
        Values = ConfigManager:AllConfigs(),
        Value  = nil,
        AllowNone = true,
        Flag   = "configSelect",
        Callback = function(_) end,
    })

    local configInput = configSec:Input({
        Title       = "Config Name",
        Desc        = "Name for saving a new config.",
        Placeholder = "e.g. default",
        Value       = "default",
        Flag        = "configName",
        Callback    = function(_) end,
    })

    configSec:Space()

    local configStack = configSec:HStack({ AutoSpace = true })

    configStack:Button({
        Title   = "Save",
        Icon    = "save",
        Justify = "Center",
        Color   = Color3.fromHex("#34D399"),
        Callback = function()
            local name = configInput.Value or "default"
            name = tostring(name):gsub("[^%w_%-]", "_")
            if name == "" then name = "default" end
            local cfg = ConfigManager:Config(name)
            cfg:Save()
            configDropdown:Refresh(ConfigManager:AllConfigs())
            WindUI:Notify({ Title = "Config", Content = 'Saved "' .. name .. '".', Icon = "save", Duration = 3 })
        end,
    })

    configStack:Button({
        Title   = "Load",
        Icon    = "folder-open",
        Justify = "Center",
        Color   = Color3.fromHex("#60A5FA"),
        Callback = function()
            local selected = configDropdown.Value
            if not selected or selected == "" then
                WindUI:Notify({ Title = "Config", Content = "Select a config first.", Icon = "alert-circle", Duration = 3 })
                return
            end
            local cfg = ConfigManager:Config(selected)
            cfg:Load()
            WindUI:Notify({ Title = "Config", Content = 'Loaded "' .. selected .. '".', Icon = "folder-open", Duration = 3 })
        end,
    })

    configStack:Button({
        Title   = "Delete",
        Icon    = "trash-2",
        Justify = "Center",
        Color   = Color3.fromHex("#EF4444"),
        Callback = function()
            local selected = configDropdown.Value
            if not selected or selected == "" then
                WindUI:Notify({ Title = "Config", Content = "Select a config first.", Icon = "alert-circle", Duration = 3 })
                return
            end
            -- Use WindUI's built-in DeleteConfig API (uses delfile internally)
            local ok, err = ConfigManager:DeleteConfig(selected)
            if not ok then
                -- Fallback: manual delete via the correct config path
                local path = "WindUI/" .. Window.Folder .. "/config/" .. selected .. ".json"
                pcall(function()
                    if delfile then
                        delfile(path)
                    elseif syn and syn.io and syn.io.delete then
                        syn.io.delete(path)
                    end
                end)
            end
            configDropdown:Refresh(ConfigManager:AllConfigs())
            WindUI:Notify({ Title = "Config", Content = 'Deleted "' .. selected .. '".', Icon = "trash-2", Duration = 3 })
        end,
    })

    configSec:Space()

    configSec:Button({
        Title    = "Refresh List",
        Icon     = "refresh-cw",
        Justify  = "Center",
        Callback = function()
            configDropdown:Refresh(ConfigManager:AllConfigs())
            WindUI:Notify({ Title = "Config", Content = "Config list refreshed.", Duration = 2 })
        end,
    })

    SettingsTab:Space()
    SettingsTab:Button({
        Title = "Destroy Hub", Icon = "trash-2", Justify = "Center",
        Color = Color3.fromHex("#EF4444"),
        Desc  = "Removes this hub completely",
        Callback = function()
            stopAutoMerge()
            stopAutoLock()
            stopAllAutoUpgrades()
            stopAutoLeave()
            stopAutoRejoin()
            stopAntiAfk()
            if holdStartedConn then holdStartedConn:Disconnect() end
            if holdEndedConn   then holdEndedConn:Disconnect()   end
            Window:Destroy()
        end,
    })
end

-- ──────────────────────────────────────────────────────────────
-- Done
-- ──────────────────────────────────────────────────────────────
task.wait(1)
WindUI:Notify({
    Title   = "Merge a Nuke  v1.4.0",
    Content = "Loaded! v1.4.0",
    Icon    = "solar:atom-bold",
    Duration = 6,
})

-- ──────────────────────────────────────────────────────────────
-- Auto-load "default" config on every script start.
--
-- WHY THE MANUAL SYNC IS NEEDED:
-- WindUI's cfg:Load() calls :Set() on each element to restore its
-- visual / stored value, but intentionally does NOT fire the
-- element's Callback.  This means toggles appear ON but nothing
-- actually starts (autoMerge loop, autoLock loop, etc.) and
-- slider values are never written back into State.xxx.
-- We fix this by reading WindUI.Flags after Load() and explicitly
-- starting every feature whose flag came back true, and applying
-- every slider value into State.
-- ──────────────────────────────────────────────────────────────
task.spawn(function()
    task.wait(1.5)  -- ensure WindUI has registered all element flags

    local ConfigManager = Window.ConfigManager

    -- Attempt load; silently skip if "default" config doesn't exist yet
    pcall(function() ConfigManager:Config("default"):Load() end)
    task.wait(0.3)  -- let WindUI finish calling :Set() on every element

    local F = WindUI.Flags
    if not F then
        warn("[Config] WindUI.Flags not available — cannot restore state.")
        return
    end

    local function flagOn(name)
        return F[name] and F[name].Value == true
    end
    local function flagVal(name)
        return F[name] and F[name].Value
    end

    -- ── Restore slider-driven State values ───────────────────
    local v
    v = flagVal("mergeDelay");      if v then State.autoMergeDelay  = v end
    v = flagVal("rejoinDelay");     if v then State.rejoinDelay      = v end
    v = flagVal("detectionRadius"); if v then State.detectionRadius  = v end
    v = flagVal("rejoinInterval");  if v then State.autoRejoinMinutes = v end
    v = flagVal("walkSpeed")
    if v then
        State.walkSpeed = v
        local hum = getHumanoid(); if hum then hum.WalkSpeed = v end
    end
    v = flagVal("jumpPower")
    if v then
        State.jumpPower = v
        local hum = getHumanoid(); if hum then hum.JumpPower = v end
    end

    -- ── Boot features whose toggle was ON ────────────────────
    if flagOn("autoMerge") then
        if R_PickUp and R_MergeRequest and R_HoldStarted then
            startAutoMerge()
        end
    end

    if flagOn("autoLock") then
        if R_RequestLock then startAutoLock() end
    end

    if flagOn("autoLeave")  then startAutoLeave()  end
    if flagOn("autoRejoin") then startAutoRejoin() end
    if flagOn("antiAfk")    then startAntiAfk()    end

    if flagOn("autoUpg_TIER")     then startAutoUpgrade("TIER")     end
    if flagOn("autoUpg_MAX")      then startAutoUpgrade("MAX")       end
    if flagOn("autoUpg_LOCKBASE") then startAutoUpgrade("LOCKBASE")  end

    -- UI-only flags (no feature to start, but apply them)
    v = flagVal("uiScale"); if v then pcall(function() Window:SetUIScale(v) end) end
    v = flagVal("toggleKey")
    if v then pcall(function() Window:SetToggleKey(Enum.KeyCode[v]) end) end

    WindUI:Notify({
        Title    = "Config",
        Content  = 'Restored settings from "default" config.',
        Icon     = "folder-open",
        Duration = 3,
    })
end)
