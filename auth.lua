--[[
    StormX Auth — Roblox single-file module (Studio plugin / loader).
    No watchdog. Returns Auth table; use Auth.protect() to halt script if blocked.
]]

local Auth = {
    LOADED = true,
    VERSION = "1.3.1",
    DISCORD_TIMEOUT = 600,
}

local CLIENT_TYPE = "roblox lua"

-- ////////// embedded crypto (pure Luau, no external requires) //////////

local bit32 = bit32

local function hex_encode(s)
    return (s:gsub(".", function(c)
        return string.format("%02x", string.byte(c))
    end))
end

local function hex_decode(h)
    return (h:gsub("..", function(cc)
        return string.char(tonumber(cc, 16))
    end))
end

local b64chars = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"

local function base64_decode(data)
    data = data:gsub("[^" .. b64chars .. "=]", "")
    return (data:gsub(".", function(x)
        if x == "=" then
            return ""
        end
        local r, f = "", (b64chars:find(x) - 1)
        for i = 6, 1, -1 do
            r = r .. (f % 2^i - f % 2^(i - 1) > 0 and "1" or "0")
        end
        return r
    end):gsub("%d%d%d?%d?%d?%d?%d?%d?", function(x)
        if #x ~= 8 then
            return ""
        end
        local c = 0
        for i = 1, 8 do
            c = c + (x:sub(i, i) == "1" and 2^(8 - i) or 0)
        end
        return string.char(c)
    end))
end

local function random_bytes(n)
    local out = table.create(n)
    for i = 1, n do
        out[i] = string.char(math.random(0, 255))
    end
    return table.concat(out)
end

local function pack_u64(n)
    local t = table.create(8)
    for i = 8, 1, -1 do
        t[i] = string.char(n % 256)
        n = math.floor(n / 256)
    end
    return table.concat(t)
end

local function unpack_u64(s)
    local n = 0
    for i = 1, 8 do
        n = n * 256 + s:byte(i)
    end
    return n
end

-- SHA-256 (compact pure Luau)
local K = {
    0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5,0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5,
    0xd807aa98,0x12835b01,0x243185be,0x550c7dc3,0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174,
    0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc,0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da,
    0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7,0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967,
    0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13,0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85,
    0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3,0xd192e819,0xd6990624,0xf40e3585,0x106aa070,
    0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5,0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3,
    0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208,0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2,
}
local function rrotate(x, n) return bit32.bor(bit32.rshift(x, n), bit32.lshift(x, 32 - n)) end
local function sha256(msg)
    local h0,h1,h2,h3,h4,h5,h6,h7 = 0x6a09e667,0xbb67ae85,0x3c6ef372,0xa54ff53a,0x510e527f,0x9b05688c,0x1f83d9ab,0x5be0cd19
    local len = #msg
    local chunks = math.floor((len + 9) / 64) + 1
    local total = chunks * 64
    local buf = table.create(total)
    for i = 1, len do buf[i] = string.byte(msg, i) end
    buf[len + 1] = 0x80
    for i = len + 2, total - 8 do buf[i] = 0 end
    local bitlen = len * 8
    for i = total, total - 7, -1 do
        buf[i] = bitlen % 256
        bitlen = math.floor(bitlen / 256)
    end
    for off = 1, total, 64 do
        local w = table.create(64)
        for i = 0, 15 do
            local j = off + i * 4
            w[i] = bit32.bor(bit32.lshift(buf[j],24), bit32.lshift(buf[j+1],16), bit32.lshift(buf[j+2],8), buf[j+3])
        end
        for i = 16, 63 do
            local s0 = bit32.bxor(rrotate(w[i-15],7), rrotate(w[i-15],18), bit32.rshift(w[i-15],3))
            local s1 = bit32.bxor(rrotate(w[i-2],17), rrotate(w[i-2],19), bit32.rshift(w[i-2],10))
            w[i] = (w[i-16] + s0 + w[i-7] + s1) % 0x100000000
        end
        local a,b,c,d,e,f,g,h = h0,h1,h2,h3,h4,h5,h6,h7
        for i = 0, 63 do
            local S1 = bit32.bxor(rrotate(e,6), rrotate(e,11), rrotate(e,25))
            local ch = bit32.bxor(bit32.band(e,f), bit32.band(bit32.bnot(e),g))
            local t1 = (h + S1 + ch + K[i+1] + w[i]) % 0x100000000
            local S0 = bit32.bxor(rrotate(a,2), rrotate(a,13), rrotate(a,22))
            local maj = bit32.bxor(bit32.band(a,b), bit32.band(a,c), bit32.band(b,c))
            local t2 = (S0 + maj) % 0x100000000
            h,g,f,e,d,c,b,a = g,f,e,(d+t1)%0x100000000,c,b,a,(t1+t2)%0x100000000
        end
        h0,h1,h2,h3,h4,h5,h6,h7 = (h0+a)%0x100000000,(h1+b)%0x100000000,(h2+c)%0x100000000,(h3+d)%0x100000000,
            (h4+e)%0x100000000,(h5+f)%0x100000000,(h6+g)%0x100000000,(h7+h)%0x100000000
    end
    local function pack(x)
        return string.char(
            bit32.rshift(x,24)%256, bit32.rshift(x,16)%256, bit32.rshift(x,8)%256, x%256
        )
    end
    return pack(h0)..pack(h1)..pack(h2)..pack(h3)..pack(h4)..pack(h5)..pack(h6)..pack(h7)
end

local function hmac_sha256(key, data)
    if #key > 64 then
        key = sha256(key)
    end
    key = key .. string.rep("\0", 64 - #key)
    local ipad, opad = {}, {}
    for i = 1, 64 do
        ipad[i] = string.char(bit32.bxor(key:byte(i), 0x36))
        opad[i] = string.char(bit32.bxor(key:byte(i), 0x5c))
    end
    return sha256(table.concat(opad) .. sha256(table.concat(ipad) .. data))
end

local function hkdf_derive(shared, client_nonce, server_nonce, version_id, session_id)
    local salt = client_nonce .. server_nonce
    local info = "stormx-auth-v1:" .. version_id .. ":" .. session_id
    local prk = hmac_sha256(salt, shared)
    local t, out = "", ""
    local i = 0
    while #out < 72 do
        i += 1
        t = hmac_sha256(prk, t .. info .. string.char(i))
        out ..= t
    end
    return {
        c2s_key = out:sub(1, 32),
        s2c_key = out:sub(33, 64),
        c2s_salt = out:sub(65, 68),
        s2c_salt = out:sub(69, 72),
    }
end

local function get_crypt()
    local ok, res = pcall(function()
        return crypt or (syn and syn.crypt) or (fluxus and fluxus.crypt) or (Sentinel and Sentinel.crypt) or _G.crypt
    end)
    return ok and res or nil
end

local function need_crypt()
    local C = get_crypt()
    if not C then
        Auth.halt("executor crypt library required for StormX crypto")
    end
    return C
end

local function normalize_key_bytes(key)
    if type(key) ~= "string" then
        return key
    end
    if #key == 32 then
        return key
    end
    if #key == 64 and key:match("^[0-9a-fA-F]+$") then
        return hex_decode(key)
    end
    local C = get_crypt()
    if C then
        local dec = C.base64decode or C.base64_decode or C.base64d
        if typeof(dec) == "function" then
            local ok, raw = pcall(dec, key)
            if ok and type(raw) == "string" and #raw == 32 then
                return raw
            end
        end
    end
    if #key >= 40 and #key <= 48 then
        local raw = base64_decode(key)
        if #raw == 32 then
            return raw
        end
    end
    Auth.halt("crypt key format invalid (expected 32 bytes, got " .. tostring(#key) .. ")")
end

local function x25519_keypair()
    local C = need_crypt()
    local gen_fn = C.generatekey or C.generate_key or C.generatekeypair or C.generate_keypair
    local comp_fn = C.computekey or C.compute_key
    if not gen_fn or not comp_fn then
        Auth.halt("crypt x25519 not available (need generatekey + computekey)")
    end

    local ok, sk, pk = pcall(gen_fn)
    if ok and sk and pk then
        sk = normalize_key_bytes(sk)
        pk = normalize_key_bytes(pk)
        if #sk == 32 and #pk == 32 then
            return sk, pk
        end
    end

    local ok2, sk_only = pcall(gen_fn)
    if not ok2 or not sk_only then
        Auth.halt("crypt generatekey failed")
    end
    sk_only = normalize_key_bytes(sk_only)

    local ok3, derived_pk = pcall(comp_fn, sk_only)
    if not ok3 or not derived_pk then
        Auth.halt("crypt computekey failed")
    end
    derived_pk = normalize_key_bytes(derived_pk)

    if #sk_only ~= 32 or #derived_pk ~= 32 then
        Auth.halt("crypt x25519 keys must be 32 bytes (sk=" .. #sk_only .. " pk=" .. #derived_pk .. ")")
    end
    return sk_only, derived_pk
end

local function x25519_shared(sk, pk)
    local C = need_crypt()
    local comp_fn = C.computekey or C.compute_key or C.computeshared or C.compute_shared
    if not comp_fn then
        Auth.halt("crypt x25519 shared secret not available")
    end
    sk = normalize_key_bytes(sk)
    pk = normalize_key_bytes(pk)
    local ok, shared = pcall(comp_fn, sk, pk)
    if not ok or not shared then
        Auth.halt("crypt shared secret failed")
    end
    shared = normalize_key_bytes(shared)
    if #shared ~= 32 then
        Auth.halt("crypt shared secret invalid length (" .. #shared .. ")")
    end
    return shared
end

local function aes_gcm_encrypt(key, iv, aad, plaintext)
    local C = need_crypt()
    local enc_fn = C.encrypt or C.aes_encrypt or C.aesencrypt
    if enc_fn then
        local ok, res = pcall(enc_fn, "aes-256-gcm", plaintext, key, iv, aad)
        if ok and res then
            return res
        end
        local ok2, res2 = pcall(enc_fn, plaintext, key, iv, aad)
        if ok2 and res2 then
            return res2
        end
    end
    if C.custom and C.custom.aes_gcm_encrypt then
        return C.custom.aes_gcm_encrypt(key, iv, aad, plaintext)
    end
    Auth.halt("crypt aes-256-gcm encrypt not available")
end

local function aes_gcm_decrypt(key, iv, aad, ciphertext)
    local C = need_crypt()
    local dec_fn = C.decrypt or C.aes_decrypt or C.aesdecrypt
    if dec_fn then
        local ok, res = pcall(dec_fn, "aes-256-gcm", ciphertext, key, iv, aad)
        if ok and res then
            return res
        end
        local ok2, res2 = pcall(dec_fn, ciphertext, key, iv, aad)
        if ok2 and res2 then
            return res2
        end
    end
    if C.custom and C.custom.aes_gcm_decrypt then
        return C.custom.aes_gcm_decrypt(key, iv, aad, ciphertext)
    end
    Auth.halt("crypt aes-256-gcm decrypt not available")
end

local function ed25519_verify(pub, msg, sig)
    local C = need_crypt()
    if C.verify then
        local ok, res = pcall(C.verify, "ed25519", msg, sig, pub)
        if ok then
            return res
        end
    end
    if C.custom and C.custom.ed25519_verify then
        return C.custom.ed25519_verify(pub, msg, sig)
    end
    Auth.halt("crypt ed25519 verify not available")
end

local function box_seal(recipient_pk, message)
    local C = need_crypt()
    if C.box and C.box.seal then
        return C.box.seal(message, recipient_pk)
    end
    if C.custom and C.custom.box_seal then
        return C.custom.box_seal(recipient_pk, message)
    end
    Auth.halt("crypt box seal not available")
end

local function pad_frame(data)
    local buckets = { 128, 256, 512 }
    local target = 512
    for _, b in ipairs(buckets) do
        if #data + 4 <= b then
            target = b
            break
        end
    end
    local header = string.char(math.floor(#data / 256) % 256, #data % 256)
    return header .. data .. random_bytes(math.max(0, target - #data - 2))
end

local function unpad_frame(data)
    local ln = data:byte(1) * 256 + data:byte(2)
    return data:sub(3, 2 + ln)
end

local function seal_license_key(seal_pub_hex, license_key)
    local recipient = hex_decode(seal_pub_hex)
    local sealed = box_seal(recipient, license_key)
    return hex_encode(sealed)
end

local function perform_init_verify(data, client_eph_pub_hex, client_nonce_hex, client_sk, version_id, sign_pub_hex)
    local server_eph_pub = hex_decode(data.server_eph_pub)
    local server_nonce = hex_decode(data.server_nonce)
    local client_eph_pub = hex_decode(client_eph_pub_hex)
    local client_nonce = hex_decode(client_nonce_hex)
    local session_id = data.session_id
    local shared = x25519_shared(client_sk, server_eph_pub)
    local sig_payload = sha256(server_eph_pub .. server_nonce .. client_eph_pub .. client_nonce .. session_id .. version_id)
    if not ed25519_verify(hex_decode(sign_pub_hex), sig_payload, hex_decode(data.signature)) then
        error("server signature verification failed")
    end
    return hkdf_derive(shared, client_nonce, server_nonce, version_id, session_id)
end

local function encrypt_frame(keys, plaintext, aad, seq)
    local padded = pad_frame(plaintext)
    local nonce = keys.c2s_salt .. pack_u64(seq)
    return pack_u64(seq) .. aes_gcm_encrypt(keys.c2s_key, nonce, aad, padded)
end

local function decrypt_frame(keys, frame, aad, seq, direction)
    if unpack_u64(frame:sub(1, 8)) ~= seq then
        error("sequence mismatch")
    end
    local key = direction == "s2c" and keys.s2c_key or keys.c2s_key
    local salt = direction == "s2c" and keys.s2c_salt or keys.c2s_salt
    local nonce = salt .. pack_u64(seq)
    return unpad_frame(aes_gcm_decrypt(key, nonce, aad, frame:sub(9)))
end

-- ////////// Roblox services //////////

local function get_services()
    local ok, HttpService = pcall(function()
        return game:GetService("HttpService")
    end)
    if not ok then
        error("Roblox HttpService required")
    end
    local Analytics
    pcall(function()
        Analytics = game:GetService("RbxAnalyticsService")
    end)
    return HttpService, Analytics
end

local HttpService, Analytics = get_services()

local function json_encode(t)
    return HttpService:JSONEncode(t)
end

local function json_decode(s)
    return HttpService:JSONDecode(s)
end

function Auth.log(...)
    print("[StormX]", ...)
end

function Auth.halt(reason)
    warn("[StormX] " .. tostring(reason or "blocked"))
    while true do
        task.wait(1e9)
    end
end

local function normalize_server(server)
    server = server:gsub("^%s+", ""):gsub("%s+$", ""):gsub("/+$", "")
    if server == "" then
        error("server URL required")
    end
    if not server:find("^https?://") and not server:find("^wss?://") then
        server = "https://" .. server
    end
    return server
end

local function http_base(server)
    server = normalize_server(server)
    if server:find("^wss?://") then
        local scheme, rest = server:match("^(wss?)://(.+)$")
        local http_scheme = scheme == "wss" and "https" or "http"
        return http_scheme .. "://" .. rest:match("^[^/]+")
    end
    local scheme, rest = server:match("^(https?)://([^/]+)")
    if scheme and rest then
        return scheme .. "://" .. rest
    end
    return server
end

local function ws_base(server)
    local base = http_base(server)
    return base:gsub("^https://", "wss://"):gsub("^http://", "ws://")
end

local function resolve_api_path(server_base, path)
    if path:find("^https?://") then
        return path
    end
    if path:sub(1, 1) ~= "/" then
        path = "/" .. path
    end
    return server_base:gsub("/+$", "") .. path
end

local exec_request = (syn and syn.request) or (http and http.request) or request or (_G and _G.http_request)

local function http_request(method, url, body, headers)
    headers = headers or {}
    if body then
        headers["Content-Type"] = "application/json"
    end
    local payload = body and json_encode(body) or nil

    if typeof(exec_request) == "function" and exec_request ~= http_request then
        local ok, res = pcall(exec_request, {
            Url = url,
            Method = method,
            Headers = headers,
            Body = payload,
        })
        if ok and res then
            local status = res.StatusCode or res.Status
            local success = res.Success
            if success == nil and status then
                success = (status >= 200 and status < 300)
            end
            if success then
                local resp_body = res.Body or ""
                if resp_body == "" then
                    return {}
                end
                return json_decode(resp_body)
            else
                error("HTTP " .. tostring(status or "failed") .. " " .. url)
            end
        end
    end

    local res = HttpService:RequestAsync({
        Url = url,
        Method = method,
        Headers = headers,
        Body = payload,
    })
    if not res.Success then
        error("HTTP " .. tostring(res.StatusCode) .. " " .. url)
    end
    if res.Body == "" then
        return {}
    end
    return json_decode(res.Body)
end

local function collect_roblox_info()
    local user_id = 0
    local username = ""
    pcall(function()
        local Players = game:GetService("Players")
        local lp = Players.LocalPlayer
        if lp then
            user_id = lp.UserId
            username = lp.Name
        end
    end)

    local client_id = "roblox"
    local exec_gethwid = gethwid or get_hwid or (_G and (_G.gethwid or _G.get_hwid))
    if typeof(exec_gethwid) == "function" then
        local ok, id = pcall(exec_gethwid)
        if ok and type(id) == "string" and id ~= "" then
            client_id = id
        end
    end

    if client_id == "roblox" then
        pcall(function()
            if Analytics then
                client_id = Analytics:GetClientId()
            end
        end)
    end

    local place_id = "0"
    local job_id = ""
    pcall(function()
        place_id = tostring(game.PlaceId)
        job_id = tostring(game.JobId)
    end)

    local device_type = "unknown"
    pcall(function()
        local UserInputService = game:GetService("UserInputService")
        device_type = tostring(UserInputService:GetPlatform())
    end)

    return {
        roblox_user_id = tostring(user_id),
        username = username:sub(1, 64),
        place_id = place_id,
        job_id = job_id:sub(1, 64),
        client_id = client_id:sub(1, 128),
        device_type = device_type,
        client_type = CLIENT_TYPE,
    }
end

local function collect_hwid(device_info)
    local user_id = device_info.roblox_user_id or "0"
    local client_id = device_info.client_id or "roblox"
    local place_id = device_info.place_id or "0"
    local joined = table.concat({ "roblox", user_id, client_id, place_id }, "|")
    return {
        cpu_signature = "roblox",
        disk_serial = user_id:sub(1, 128),
        mac_address = place_id:sub(1, 32),
        board_serial = client_id:sub(1, 128),
        system_uuid = (device_info.username or ""):sub(1, 128),
        hwid_hash = hex_encode(sha256(joined)),
    }
end

local function open_discord(http_base_url, link_path)
    local origin = http_base_url
    local url = resolve_api_path(origin, link_path)
    local redirect_uri = origin:gsub("/+$", "") .. "/stormx/auth/discord/callback"
    url = url .. (url:find("?") and "&" or "?") .. "redirect_uri=" .. HttpService:UrlEncode(redirect_uri)
    if not url:find("format=") then
        url = url .. "&format=json"
    end
    local body = http_request("GET", url, nil, {})
    if not body.success then
        error(body.message or "discord link failed")
    end
    local data = body.data or {}
    local open_url = data.app_url or data.web_url
    if not open_url or open_url == "" then
        error("no discord oauth url")
    end
    if plugin and plugin.OpenBrowserWindow then
        Auth.log("Opening Discord link in browser...")
        plugin:OpenBrowserWindow(open_url)
        return open_url
    end
    if typeof(setclipboard) == "function" then
        setclipboard(open_url)
        Auth.log("Discord URL copied to clipboard — open browser and complete login.")
    else
        Auth.log("Link Discord:", open_url)
    end
    return open_url
end

local function parse_license_key(license_key)
    local key = license_key:upper():gsub("^%s+", ""):gsub("%s+$", "")
    local prefix, slug = key:match("^([A-Z0-9]+)%-([A-Z0-9]+)%-[A-Z0-9]+$")
    if not prefix then
        error("invalid license key format")
    end
    return prefix, slug
end

local function resolve_product(server, license_key)
    local prefix, slug = parse_license_key(license_key)
    local url = string.format("%s/stormx/auth/products/%s/%s", http_base(server), prefix, slug)
    local body = http_request("GET", url, nil, {})
    if not body.success then
        error(body.message or "product lookup failed")
    end
    local data = body.data
    if typeof(data) ~= "table" then
        error("product catalog unavailable")
    end
    return {
        version_id = string.lower(tostring(data.version_id)),
        name = data.name or "",
        prefix = data.prefix or prefix,
        slug = data.slug or slug,
        sign_pub_key = data.sign_pub_key,
        seal_pub_key = data.seal_pub_key,
    }
end

local Client = {}
Client.__index = Client

function Client.new(version_id, server, sign_pub_key, seal_pub_key)
    return setmetatable({
        version_id = string.lower(version_id),
        server = normalize_server(server),
        sign_pub_key = sign_pub_key,
        seal_pub_key = seal_pub_key,
        session_id = nil,
        roblox_user_id = 0,
        device_info = nil,
        keys = nil,
        ws = nil,
        authenticated = false,
        c2s_seq = 0,
        s2c_seq = 0,
        login_data = {},
        hwid_data = {},
        last_link_url = nil,
        _inbox = nil,
        _opened = false,
    }, Client)
end

function Client:init()
    self.device_info = collect_roblox_info()
    self.roblox_user_id = tonumber(self.device_info.roblox_user_id) or 0
    if self.roblox_user_id <= 0 then
        Auth.halt("roblox user id required (wait for LocalPlayer)")
    end
    self.hwid_data = collect_hwid(self.device_info)

    local client_nonce = hex_encode(random_bytes(32))
    local url = string.format(
        "%s/stormx/auth/versions/%s/init/roblox",
        http_base(self.server),
        self.version_id
    )
    local body = http_request("POST", url, {
        client_type = CLIENT_TYPE,
        roblox_user_id = self.roblox_user_id,
        client_nonce = client_nonce,
        device_info = self.device_info,
    }, {})
    if body.success == false then
        Auth.halt(body.message or "init failed")
    end
    local data = body.data or {}
    self.session_id = data.session_id
    self.sign_pub_key = data.sign_pub_key or self.sign_pub_key
    self.seal_pub_key = data.seal_pub_key or self.seal_pub_key
    if not self.session_id then
        Auth.halt("init failed: no session")
    end
    Auth.log("Session ready (user " .. tostring(self.roblox_user_id) .. ")")
    return data
end

function Client:connect()
    if not self.session_id then
        self:init()
    end
end

function Client:login(license_key)
    if not self.session_id then
        self:init()
    end
    local url = string.format(
        "%s/stormx/auth/versions/%s/login",
        http_base(self.server),
        self.version_id
    )
    local body = http_request("POST", url, {
        session_id = self.session_id,
        license_key = license_key,
        client_type = CLIENT_TYPE,
        roblox_user_id = self.roblox_user_id,
        device_info = self.device_info,
        hwid = self.hwid_data,
    }, {})
    if body.success == false then
        error(body.message or "login request failed")
    end
    local data = body.data or {}
    self.login_data = data
    self.authenticated = data.success == true
    if data.link_url then
        self.last_link_url = data.link_url
    end
    return self.authenticated
end

function Client:heartbeat()
    local url = string.format(
        "%s/stormx/auth/versions/%s/heartbeat",
        http_base(self.server),
        self.version_id
    )
    local body = http_request("POST", url, {
        session_id = self.session_id,
    }, {})
    local data = body.data or {}
    return data.ok == true
end

function Client:discord_info()
    local url = string.format(
        "%s/stormx/auth/versions/%s/discord?session_id=%s",
        http_base(self.server),
        self.version_id,
        self.session_id
    )
    local body = http_request("GET", url, nil, {})
    return body.data or {}
end

function Client:link_discord()
    if not self.last_link_url then
        error("login first")
    end
    return open_discord(http_base(self.server), self.last_link_url)
end

function Client:wait_for_discord_link(timeout)
    timeout = timeout or Auth.DISCORD_TIMEOUT
    local deadline = os.clock() + timeout
    while os.clock() < deadline do
        local info = Client.discord_info(self)
        if info.linked then
            return info
        end
        task.wait(2)
    end
    return Client.discord_info(self)
end

function Client:close()
    if self.ws then
        pcall(function()
            self.ws:Close()
        end)
        self.ws = nil
    end
end

function Auth.new(server, license_key)
    if not Auth.LOADED then
        Auth.halt("auth module not loaded")
    end
    license_key = license_key:gsub("^%s+", ""):gsub("%s+$", "")
    if license_key == "" then
        error("license_key required")
    end
    local product = resolve_product(server, license_key)
    local self = {
        server = normalize_server(server),
        license_key = license_key,
        product = product,
        _client = Client.new(product.version_id, server, product.sign_pub_key, product.seal_pub_key),
    }
    return setmetatable(self, { __index = Auth })
end

function Auth:authenticate(timeout)
    Auth.log("Initializing Roblox session...")
    self._client:init()
    Auth.log("Logging in...")
    if not self._client:login(self.license_key) then
        Auth.log("Login failed:", self._client.login_data.message or "unknown")
        return false
    end
    if self:_discord_satisfied() then
        Auth.log("Authenticated (Discord already linked)")
        return true
    end
    Auth.log("Discord link required — waiting for OAuth...")
    self._client:link_discord()
    local info = self._client:wait_for_discord_link(timeout)
    if info.linked then
        self._client.login_data.discord_linked = true
        self._client.login_data.discord_id = info.discord_id
        self._client.login_data.discord_username = info.discord_username
        Auth.log("Discord linked:", info.discord_username or info.discord_id or "ok")
    end
    return info.linked == true
end

function Auth:_discord_satisfied()
    local data = self._client.login_data or {}
    if data.discord_linked or data.discord_id then
        return true
    end
    local ok, info = pcall(function()
        return Client.discord_info(self._client)
    end)
    return ok and info and info.linked == true
end

function Auth:discord_info()
    local ok, info = pcall(function()
        return Client.discord_info(self._client)
    end)
    if ok and type(info) == "table" then
        return info
    end
    return self._client.login_data or {}
end

function Auth:user_info()
    local login = self._client.login_data or {}
    local device = self._client.device_info or {}
    return {
        user_id = login.user_id,
        license_key_id = login.license_key_id,
        product_name = self.product.name,
        product = self.product.prefix .. "-" .. self.product.slug,
        version_id = self.product.version_id,
        key_prefix = login.key_prefix,
        hwid_hash = login.hwid_hash or self._client.hwid_data.hwid_hash,
        roblox_user_id = self._client.roblox_user_id,
        roblox_username = device.username,
        client_type = CLIENT_TYPE,
        discord_linked = login.discord_linked == true or login.discord_id ~= nil,
        discord_id = login.discord_id,
        discord_username = login.discord_username,
        require_discord = login.require_discord ~= false,
        expires_at = login.expires_at,
    }
end

function Auth:heartbeat()
    return self._client:heartbeat()
end

function Auth:close()
    self._client:close()
end

--- Load auth.lua, authenticate, then run callback. Halts forever on any failure.
function Auth.protect(callback, server, license_key, timeout)
    if not Auth.LOADED then
        Auth.halt("auth.lua not loaded")
    end
    Auth.log("StormX Auth v" .. Auth.VERSION)
    local ok, auth_or_err = pcall(Auth.new, server, license_key)
    if not ok then
        Auth.halt("auth init failed: " .. tostring(auth_or_err))
    end
    local auth = auth_or_err
    local ok2, authed = pcall(function()
        return auth:authenticate(timeout)
    end)
    if not ok2 or not authed then
        pcall(function()
            auth:close()
        end)
        Auth.halt("authentication failed")
    end
    local ok3, result = pcall(callback, auth)
    pcall(function()
        auth:close()
    end)
    if not ok3 then
        Auth.halt("script error: " .. tostring(result))
    end
    return result
end

return Auth
