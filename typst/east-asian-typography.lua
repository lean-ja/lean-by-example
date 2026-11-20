-- IntroductionLean の設定に倣い、日本語の改行やインライン装飾の前後に
-- Markdown 由来の余分な空白が入るのを防ぐ。英文の単語間空白は維持する。

local function is_east_asian_wide(codepoint)
  return
    (codepoint >= 0x1100 and codepoint <= 0x115F) or
    (codepoint >= 0x2329 and codepoint <= 0x232A) or
    (codepoint >= 0x2E80 and codepoint <= 0xA4CF) or
    (codepoint >= 0xAC00 and codepoint <= 0xD7A3) or
    (codepoint >= 0xF900 and codepoint <= 0xFAFF) or
    (codepoint >= 0xFE10 and codepoint <= 0xFE19) or
    (codepoint >= 0xFE30 and codepoint <= 0xFE6F) or
    (codepoint >= 0xFF01 and codepoint <= 0xFF60) or
    (codepoint >= 0xFFE0 and codepoint <= 0xFFE6) or
    (codepoint >= 0x1B000 and codepoint <= 0x1B2FF) or
    (codepoint >= 0x20000 and codepoint <= 0x3FFFD)
end

local function visible_text(inline)
  if inline.t == "Span" or inline.t == "Strong" or inline.t == "Emph" or inline.t == "Link" then
    local parts = {}
    for _, child in ipairs(inline.content) do
      parts[#parts + 1] = visible_text(child)
    end
    return table.concat(parts)
  end
  return pandoc.utils.stringify(inline)
end

local function first_codepoint(inline)
  local text = visible_text(inline)
  if text == "" then
    return nil
  end
  return utf8.codepoint(text, 1)
end

local function last_codepoint(inline)
  local text = visible_text(inline)
  if text == "" then
    return nil
  end
  return utf8.codepoint(text, utf8.offset(text, -1))
end

local function is_compact_inline(inline)
  return inline.t == "Code" or inline.t == "Strong" or inline.t == "Emph"
end

function Inlines(inlines)
  if FORMAT ~= "typst" then
    return nil
  end

  local result = pandoc.List()
  for index, inline in ipairs(inlines) do
    local previous = inlines[index - 1]
    local following = inlines[index + 1]
    local remove = false
    if previous and following and (inline.t == "SoftBreak" or inline.t == "Space") then
      local left_wide = is_east_asian_wide(last_codepoint(previous) or 0)
      local right_wide = is_east_asian_wide(first_codepoint(following) or 0)
      if inline.t == "SoftBreak" then
        remove = left_wide and right_wide
      elseif inline.t == "Space" then
        remove = (is_compact_inline(following) and left_wide)
          or (is_compact_inline(previous) and right_wide)
      end
    end
    if not remove then
      result:insert(inline)
    end
  end
  return result
end
