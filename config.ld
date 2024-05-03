project = "lua-mdns"
title = project
file = "mdns.lua"
sort = true
convert_opt = true
-- all = true

-- can specify the Markdown processor (falls back to markdown.lua)
format = "markdown"

-- if you don't use markdown you may wish for backticks to be
-- expanded if they enclose a reference.
backtick_references = false

custom_css = "ldoc_custom.css"
style="!new"

custom_display_name_handler = function(item, default_handler)
  local name

  local function _tags(name, item, tags)
    local ftype_tpl = '<span class="ftype">[%s]</span> %s'
    tags = tags or { "constructor", "private", "static" }

    if all and "module" ~= item.type and "classmod" ~= item.type then
      -- when generating complete documentation check explicitly
      -- for a tag named by item type
      tags[#tags+1] = item.type
    end

    for _, tag in ipairs(tags) do
      if item.tags[tag] then
        name = ftype_tpl:format(tag, name)
      end
    end

    return name
  end

  if all then
    -- when generating complete documentation add explicitly
    -- a new tag named by item type
    item.tags[item.type] = true
  end

  if "field" == item.type then
    if 1 == item.kind:find("class ") then
      name = item.section:gsub("^Class ", "")
      name = name .. "." .. item.name:sub(#item.module.name + 2)
      name = _tags(name, item)
    else
      name = _tags(default_handler(item), item)
    end
  elseif ("function" == item.type) or ("lfunction" == item.type) then
    name = default_handler(item):gsub("(%s*)(%(.*)$", '%1<span class="args">%2</span>')
    name = _tags(name, item)
  elseif "classmod" == item.type then
    if not item.display_name then
      name = _tags(default_handler(item), item, {"static"})
      item.display_name = name
    end

    name = item.display_name
  elseif "macro" == item.type then
    if not item.display_name then
      name = _tags(default_handler(item), item)
      item.display_name = name
    end

    name = item.display_name
  else
    name = _tags(default_handler(item), item)
  end

  return name
end
