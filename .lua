-- ============================================================
--  Merge a Nuke Utilities  v1.2.0
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
    autoMergeDelay   = 0.5,
    stats            = { merges = 0, drops = 0, errors = 0 },
    highestTier      = 0,

    autoLockEnabled  = false,
    autoLockThread   = nil,

    autoLeaveEnabled = false,
    autoLeaveThread  = nil,

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
    while State.autoLockEnabled do
        if lockPhase == "free" then
            pcall(function() R_RequestLock:FireServer() end)
            -- Wait up to 3s for the state to change
            local t = tick()
            repeat task.wait(0.2) until lockPhase ~= "free" or (tick()-t) > 3
        elseif lockPhase == "locked" then
            -- Already locked — wait until it expires (add 1s buffer)
            local waitFor = math.max(1, lockSecondsLeft + 1)
            task.wait(waitFor)
        elseif lockPhase == "cooldown" then
            -- On cooldown — wait it out
            local waitFor = math.max(1, lockSecondsLeft + 0.5)
            task.wait(waitFor)
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
local LEAVE_DETECT_RADIUS = 75   -- studs from island center
local REJOIN_DELAY        = 2    -- seconds to wait before rejoining (lets nuke clear)
local SCRIPT_URL          = nil  -- set to your raw script URL to auto re-execute on join

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

local function doRejoin()
    pcall(function()
        -- Show countdown so user knows a rejoin is coming
        for i = REJOIN_DELAY, 1, -1 do
            WindUI:Notify({
                Title   = "Auto Leave",
                Content = "Rejoining in " .. i .. "s...",
                Icon    = "clock",
                Duration = 1.1,
            })
            task.wait(1)
        end

        -- Attempt re-execution before teleporting (executor must support setfflag or getscriptbytecode)
        -- If SCRIPT_URL is set, queue re-execution via StarterGui tag after teleport
        if SCRIPT_URL and SCRIPT_URL ~= "" then
            pcall(function()
                -- Store script URL in a LocalStorage tag so it can be recovered post-teleport
                local tag = Instance.new("StringValue")
                tag.Name  = "ManuReexec"
                tag.Value = SCRIPT_URL
                tag.Parent = game:GetService("Players").LocalPlayer
            end)
        end

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
                            if math.sqrt(dx*dx + dz*dz) <= LEAVE_DETECT_RADIUS then
                                State.autoLeaveEnabled = false
                                WindUI:Notify({ Title = "Auto Leave", Content = "Incoming nuke! Rejoining in " .. REJOIN_DELAY .. "s...", Duration = REJOIN_DELAY + 1 })
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
-- Anti-AFK
-- Prevents the Roblox AFK kick by simulating tiny character
-- movements every 20 seconds. Works by briefly jumping via
-- the VirtualUser service (same approach as Infinite Yield).
-- ──────────────────────────────────────────────────────────────
local VirtualUser = game:GetService("VirtualUser")

local function antiAfkLoop()
    while State.antiAfkEnabled do
        task.wait(20)
        if State.antiAfkEnabled then
            pcall(function()
                LocalPlayer.Idled:connect(function() end) -- suppress idle signal
                VirtualUser:Button2Down(Vector2.new(0, 0), CFrame.new())
                task.wait(0.1)
                VirtualUser:Button2Up(Vector2.new(0, 0), CFrame.new())
            end)
        end
    end
end

local function startAntiAfk()
    if State.antiAfkThread then task.cancel(State.antiAfkThread) end
    State.antiAfkEnabled = true
    State.antiAfkThread  = task.spawn(antiAfkLoop)
end

local function stopAntiAfk()
    State.antiAfkEnabled = false
    if State.antiAfkThread then task.cancel(State.antiAfkThread); State.antiAfkThread = nil end
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
    Author      = "by Claude  •  v1.1.0",
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

Window:Tag({ Title = "v1.1.0", Icon = "zap", Color = Color3.fromHex("#1a1a2e"), Border = true })

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
        Value = { Min = 0.2, Max = 3.0, Default = 0.5 }, Step = 0.1,
        IsTooltip = true, Flag = "mergeDelay",
        Callback = function(v) State.autoMergeDelay = v end,
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
        Desc  = "Keeps your island locked automatically.",
        Value = false, Flag = "autoLock",
        Callback = function(state)
            if state then
                if not R_RequestLock then
                    WindUI:Notify({ Title = "Error", Content = "RequestLockBase remote not found.", Icon = "alert-circle", Duration = 4 })
                    return
                end
                startAutoLock()
                WindUI:Notify({ Title = "Auto Lock", Content = "Started! Island will stay locked.", Icon = "shield", Duration = 3 })
            else
                stopAutoLock()
                WindUI:Notify({ Title = "Auto Lock", Content = "Stopped.", Duration = 2 })
            end
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
                local autoStr = State.autoLockEnabled and "  [Auto: ON]" or "  [Auto: OFF]"
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
            if state then startAutoUpgrade("TIER") else stopAutoUpgrade("TIER") end
        end,
    })
    upgSec:Space()

    upgSec:Toggle({
        Title = "Max Spawns", Desc = "Auto-buys Max Spawns upgrades.",
        Value = false, Flag = "autoUpg_MAX",
        Callback = function(state)
            if state then startAutoUpgrade("MAX") else stopAutoUpgrade("MAX") end
        end,
    })
    upgSec:Space()

    upgSec:Toggle({
        Title = "Lock Cooldown", Desc = "Auto-buys Lock Cooldown upgrades.",
        Value = false, Flag = "autoUpg_LOCKBASE",
        Callback = function(state)
            if state then startAutoUpgrade("LOCKBASE") else stopAutoUpgrade("LOCKBASE") end
        end,
    })
end

-- ── Auto Leave Tab ──────────────────────────────────────────
local LeaveTab = MainSection:Tab({
    Title = "Auto Leave", Icon = "log-out",
    IconColor = Color3.fromHex("#F87171"), Border = true,
})
do
    local leaveSec = LeaveTab:Section({ Title = "Auto Leave", Box = true, BoxBorder = true, Opened = true })

    leaveSec:Toggle({
        Title = "Enable Auto Leave", Icon = "log-out",
        Desc  = "Rejoins the game when an enemy nuke enters 75 studs of your island while unlocked.",
        Value = false, Flag = "autoLeave",
        Callback = function(state)
            if state then
                startAutoLeave()
                WindUI:Notify({ Title = "Auto Leave", Content = "Active. Watching for incoming nukes.", Duration = 3 })
            else
                stopAutoLeave()
                WindUI:Notify({ Title = "Auto Leave", Content = "Stopped.", Duration = 2 })
            end
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
        Desc  = "Prevents Roblox from kicking you for inactivity by simulating input every 20 seconds.",
        Value = false, Flag = "antiAfk",
        Callback = function(state)
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
        end,
    })
    moveSec:Space()
    moveSec:Slider({
        Title = "Jump Power", Value = { Min = 10, Max = 200, Default = 50 }, Step = 5,
        IsTooltip = true, Flag = "jumpPower",
        Callback = function(v)
            State.jumpPower = v
            local hum = getHumanoid(); if hum then hum.JumpPower = v end
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
        Callback = function(v) Window:SetUIScale(v) end,
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
    Title   = "Merge a Nuke  v1.2.0",
    Content = "Loaded! v1.2.0 — Anti-AFK, 75-stud leave, rejoin delay.",
    Icon    = "solar:atom-bold",
    Duration = 5,
})
