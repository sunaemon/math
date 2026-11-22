-- The formula attribute follows math nodes through TeX layout. Tag individual
-- painted glyph/rule nodes at shipout, so tags stay balanced even when inline
-- math wraps or crosses a page. No boxes, glue, widths or penalties are changed.
book_formula_overlay = book_formula_overlay or {}
local M = book_formula_overlay
if M.attribute then return end
M.attribute = luatexbase.new_attribute("book_formula_overlay")
local names, ids = {}, {}
local unset = -2147483647
function M.start(name)
  local id = ids[name]
  if not id then id = #names + 1; names[id] = name; ids[name] = id end
  tex.setattribute(M.attribute, id)
end
function M.finish() tex.setattribute(M.attribute, unset) end

local glyph, rule = node.id("glyph"), node.id("rule")
local hlist, vlist = node.id("hlist"), node.id("vlist")
local function literal(data)
  local n = node.new("whatsit", "pdf_literal")
  n.mode, n.data = 1, data
  return n
end
local function decorate(head, inherited)
  local current = head
  while current do
    local following = current.next
    local id = node.has_attribute(current, M.attribute) or inherited
    if current.id == hlist or current.id == vlist then
      current.list = decorate(current.list, id)
    elseif (current.id == glyph or current.id == rule) and id and names[id] then
      head = node.insert_before(head, current, literal("/" .. names[id] .. " BMC"))
      head = node.insert_after(head, current, literal("EMC"))
    end
    current = following
  end
  return head
end
luatexbase.add_to_callback("pre_shipout_filter", function(box)
  box.list = decorate(box.list)
  return true
end, "book_formula_overlay")
