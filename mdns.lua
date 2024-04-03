--[[

    Copyright (c) 2015 Frank Edelhaeuser

    This file is part of lua-mdns.

    Permission is hereby granted, free of charge, to any person obtaining a copy
    of this software and associated documentation files (the "Software"), to deal
    in the Software without restriction, including without limitation the rights
    to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
    copies of the Software, and to permit persons to whom the Software is
    furnished to do so, subject to the following conditions:

    The above copyright notice and this permission notice shall be included in all
    copies or substantial portions of the Software.

    THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
    IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
    FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
    AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
    LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
    OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
    SOFTWARE.

    Usage:

        local mdns = require('mdns')

        local res = mdns.query('_printer._tcp') -- find printers
        if (res) then
            for k,v in pairs(res) do
                print(k)
                local function print_table(t, indent)
                    for k,v in pairs(t) do
                        if (type(v) == 'table') then
                            print(string.rep('  ',indent)..k..':')
                            print_table(v, indent + 1)
                        else
                            print(string.rep('  ',indent)..k..': '..v)
                        end
                    end
                end
                print_table(v, 1)
            end
        else
            print('no result')
        end

]]--

local mdns = {}

local SERVICE_TYPE_META_QUERY = '_services._dns-sd._udp'
local LOCAL_DOMAIN = '.local'

--Is the service name the service type meta query?
---@param service string Service name to check
---@return boolean
local function mdns_is_meta_query(service)
    return service:sub(1,#SERVICE_TYPE_META_QUERY) == SERVICE_TYPE_META_QUERY
end

local DNS = {
    -- Resource Record (RR) TYPEs
    -- https://www.iana.org/assignments/dns-parameters/dns-parameters.xhtml#dns-parameters-4
    RR = {
        A    = 1,  -- A host address
        PTR  = 12, -- A domain name pointer
        TXT  = 16, -- Text strings
        AAAA = 28, -- IP6 Address
        SRV  = 33  -- Server selection
    }
}

local function mdns_make_query(service)
    -- header: transaction id, flags, qdcount, ancount, nscount, nrcount
    local data = '\000\000'..'\000\000'..'\000\001'..'\000\000'..'\000\000'..'\000\000'
    -- question section: qname, qtype, qclass
    for n in service:gmatch('([^%.]+)') do
        data = data..string.char(#n)..n
    end
    return data..string.char(0)..'\000\012'..'\000\001'
end

local function mdns_parse(service, data, answers)
    --- Helper function: parse DNS name field, supports pointers
    -- @param data     received datagram
    -- @param offset    offset within datagram (1-based)
    -- @return  parsed name
    -- @return  offset of first byte behind name (1-based)
    local function parse_name(data, offset)
        local n,d,l = '', '', data:byte(offset)
        while l > 0 do
            if l >= 192 then -- pointer
                local p = (l % 192) * 256 + data:byte(offset + 1)
                return n..d..parse_name(data, p + 1), offset + 2
            end
            n = n..d..data:sub(offset + 1, offset + l)
            offset = offset + l + 1
            l = data:byte(offset)
            d = '.'
        end
        return n, offset + 1
    end

    --- Helper function: check if a single bit is set in a number
    -- @param val       number
    -- @param mask      mask (single bit only)
    -- @return  true if bit is set, false if not
    local function bit_set(val, mask)
        return val % (mask + mask) >= mask
    end

    -- decode and check header
    if not data then
        return nil, 'no data'
    end
    local len = #data
    if len < 12 then
        return nil, 'truncated'
    end

    local header = {
        id = data:byte(1) * 256 + data:byte(2),
        flags = data:byte(3) * 256 + data:byte(4),
        qdcount = data:byte(5) * 256 + data:byte(6),
        ancount = data:byte(7) * 256 + data:byte(8),
        nscount = data:byte(9) * 256 + data:byte(10),
        arcount = data:byte(11) * 256 + data:byte(12),
    }
    if not bit_set(header.flags, 0x8000) then
        return nil, 'not a reply'
    end
    if bit_set(header.flags, 0x0200) then
        return nil, 'TC bit is set'
    end
    if header.ancount == 0 then
        return nil, 'no answer records'
    end

    -- skip question section
    local name
    local offset = 13
    if header.qdcount > 0 then
        for i=1, header.qdcount do
            if offset > len then
                return nil, 'truncated'
            end
            name, offset = parse_name(data, offset)
            offset = offset + 4
        end
    end


    local function process_answer(answers, data, offset)
        local type = data:byte(offset + 0) * 256 + data:byte(offset + 1)
        local rdlength = data:byte(offset + 8) * 256 + data:byte(offset + 9)
        local rdoffset = offset + 10

        -- A record (IPv4 address)
        if type == DNS.RR.A then
            if rdlength ~= 4 then
                return nil, 'bad RDLENGTH with A record'
            end
            answers.a[name] = string.format('%d.%d.%d.%d', data:byte(rdoffset, rdoffset+3))
        -- PTR record (pointer)
        elseif type == DNS.RR.PTR then
            local target = parse_name(data, rdoffset)
            table.insert(answers.ptr, target)
        -- AAAA record (IPv6 address)
        elseif type == DNS.RR.AAAA then
            if rdlength ~= 16 then
                return nil, 'bad RDLENGTH with AAAA record'
            end

            local aaaa = string.format('%x', data:byte(rdoffset)*256 + data:byte(rdoffset+1))
            for offs = rdoffset+2, rdoffset+14, 2 do
                aaaa = aaaa..':'..string.format('%x', data:byte(offs)*256 + data:byte(offs+1))
            end

            -- compress IPv6 address
            for _, s in ipairs{ ':0:0:0:0:0:0:0:', ':0:0:0:0:0:0:', ':0:0:0:0:0:', ':0:0:0:0:', ':0:0:0:', ':0:0:' } do
                local r = aaaa:gsub(s, '::', 1)
                if r ~= aaaa then
                    aaaa = r
                    break
                end
            end
            answers.aaaa[name] = aaaa
        -- SRV record (service location)
        elseif type == DNS.RR.SRV then
            if rdlength < 6 then
                return nil, 'bad RDLENGTH with SRV record'
            end
            answers.srv[name] = {
                target = parse_name(data, rdoffset + 6),
                port = data:byte(rdoffset + 4) * 256 + data:byte(rdoffset + 5)
            }
        -- TXT Text strings
        elseif type == DNS.RR.TXT then
            answers.txt[name] = answers.txt[name] or {}

            local txtoffset = rdoffset
            while txtoffset < rdoffset + rdlength do
                local txtlength = data:byte(txtoffset)
                txtoffset = txtoffset + 1

                local txt = data:sub(txtoffset, txtoffset + txtlength - 1)
                table.insert(answers.txt[name], txt)
                txtoffset = txtoffset + txtlength
            end
        end

        return true
    end

    -- evaluate answer section
    for i=1, header.ancount do
        if offset > len then
            return nil, 'truncated'
        end

        name, offset = parse_name(data, offset)
        local worked, err = process_answer(answers, data, offset)

        if worked == nil then
            return nil, err
        end

        -- next answer record
        offset = offset + 10 + (data:byte(offset + 8) * 256 + data:byte(offset + 9))
    end
-- evaluate additionals section
    if (header.arcount > 0) then
        for i=1, header.arcount do
            if offset > len then
                return nil, 'truncated'
            end

            name, offset = parse_name(data, offset)
            local worked, err = process_answer(answers, data, offset)

            if worked == nil then
                return nil, err
            end

            -- next answer record
            offset = offset + 10 + (data:byte(offset + 8) * 256 + data:byte(offset + 9))
        end
    end
    return answers
end

--Receive and parse datagram replies
---@param service string MDNS service name
---@param answers table Table of answers from query
local function mdns_recv_and_parse(service, answers)
    -- Ensure that answers has a table at the specified key
    for _, key in ipairs{ 'srv', 'a', 'aaaa', 'ptr', 'txt' } do
        answers[key] = answers[key] or {}
    end

    local data = mdns.socket:recv()
    if data then
        mdns_parse(service, data, answers)
        if mdns_is_meta_query(service) then
            for _, ptr in ipairs(answers.ptr) do
                mdns.socket:send(mdns_make_query(ptr))
            end
            answers.ptr = {}
        end
    end
end

--Extract target services from answers, resolve hostnames
---@param service string MDNS service name
---@param answers table Table of answers from query
---@return table|nil services Formatted table of services
local function mdns_results(service, answers)
    local services = {}

    if not answers.srv then
        return nil
    end

    for k,v in pairs(answers.srv) do
        local pos = k:find('%.')
        if pos and pos > 1 and pos < #k then
            local name, svc = k:sub(1, pos - 1), k:sub(pos + 1)
            if mdns_is_meta_query(service) or svc == service then
                if v.target then
                    if answers.a[v.target] then
                        v.ipv4 = answers.a[v.target]
                    end
                    if answers.aaaa[v.target] then
                        v.ipv6 = answers.aaaa[v.target]
                    end
                    if v.target:sub(-#LOCAL_DOMAIN) == LOCAL_DOMAIN then
                        v.hostname = v.target:sub(1, #v.target - 6)
                    end
                    v.target = nil
                end
                v.service = svc
                v.name = name
                v.text = answers.txt[k]
                services[k] = v
            end
        end
    end

    return services
end

---Socket options
---These are exposed to allow the user to customise
---e.g. Use IPv6, some other transport, or even a socket library other than LuaSocket
mdns.socket = {
    PEER = {
        --Destination IP
        IP = '224.0.0.251',
        --Destination port
        PORT = 5353
    },

    --LuaSocket UDP Object
    udp = nil,

    --Setup socket
    ---@param self table mdns_socket Object
    setup = function(self)
        local socket = require('socket')
        self.udp = socket.udp()
        assert(self.udp:setsockname('*', 0))
        assert(self.udp:setoption('ip-add-membership', { interface = '*', multiaddr = self.PEER.IP }))
        assert(self.udp:settimeout(0.1))
    end,

    --Send datagram
    ---@param self table mdns_socket Object
    ---@param datagram string MDNS query string
    send = function(self, datagram)
        assert(self.udp:sendto(datagram, self.PEER.IP, self.PEER.PORT))
    end,

    --Receive response datagram
    ---@param self table mdns_socket Object
    ---@return string|nil datagram Response datagram
    recv = function(self)
        local datagram, peeraddr, peerport = self.udp:receivefrom()
        if peerport == self.PEER.PORT then
            return datagram
        end
    end,

    --Tear down socket
    ---@param self table mdns_socket Object
    teardown = function(self)
        assert(self.udp:setoption('ip-drop-membership', { interface = '*', multiaddr = self.PEER.IP }))
        assert(self.udp:close())
        self.udp = nil
    end
}

--Quantify query or return special meta-query if no service name specified
---@param service? string|nil Service name
---@return string service Quantified service name to query
local function mdns_quantify_query(service)
    if not service then
        return SERVICE_TYPE_META_QUERY..LOCAL_DOMAIN
    end

    -- append .local if needed
    if service:sub(-#LOCAL_DOMAIN) ~= LOCAL_DOMAIN then
        service = service..LOCAL_DOMAIN
    end

    return service
end

--- Locate MDNS services in local network
--
-- @param service   MDNS service name to search for (e.g. _ipps._tcp). A .local postfix will
--                  be appended if needed. If this parameter is not specified, all services
--                  will be queried.
--
-- @param timeout   Number of seconds to wait for MDNS responses. The default timeout is 2
--                  seconds if this parameter is not specified.
--
-- @return          Table of MDNS services. Entry keys are service identifiers. Each entry
--                  is a table containing all or a subset of the following elements:
--
--                      name: MDNS service name (e.g. HP Laserjet 4L @ server.example.com)
--                      service: MDNS service type (e.g. _ipps._tcp.local)
--                      hostname: hostname
--                      port: port number
--                      ipv4: IPv4 address
--                      ipv6: IPv6 address
--                      text: Table of text record(s)
--
function mdns.query(service, timeout)
    -- quantify query or return special meta-query if no service name specified
    service = mdns_quantify_query(service)

    -- default timeout: 2 seconds
    timeout = timeout or 2.0

    -- create IPv4 socket for multicast DNS
    mdns.socket:setup()

    -- send query
    mdns.socket:send(mdns_make_query(service))

    -- collect responses until timeout
    local answers = {}
    local start = os.time()
    while os.time() - start < timeout do
        mdns_recv_and_parse(service, answers)
    end

    -- cleanup socket
    mdns.socket:teardown()

    -- extract target services from answers, resolve hostnames
    return mdns_results(service, answers)
end

function mdns.query_async(service)
    -- quantify query or return special meta-query if no service name specified
    service = mdns_quantify_query(service)

    -- create IPv4 socket for multicast DNS
    mdns.socket:setup()

    -- send query
    mdns.socket:send(mdns_make_query(service))

    -- create async callbacks
    local answers = {}
    local function tick()
        -- collect responses
        mdns_recv_and_parse(service, answers)
    end

    local function finalise()
        -- cleanup socket
        mdns.socket:teardown()

        -- extract target services from answers, resolve hostnames
        return mdns_results(service, answers)
    end

    -- Return async callback functions
    return tick, finalise
end

return mdns
