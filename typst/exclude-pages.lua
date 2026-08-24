local excluded_headings = {
  ["ランダムページ"] = true,
  ["ランダムぺージ"] = true,
}

function Pandoc(document)
  local blocks = {}
  local excluded_level = nil

  for _, block in ipairs(document.blocks) do
    if excluded_level ~= nil then
      if block.t == "Header" and block.level <= excluded_level then
        excluded_level = nil
      end
    end

    if excluded_level == nil then
      if block.t == "Header"
          and excluded_headings[pandoc.utils.stringify(block.content)] then
        excluded_level = block.level
      else
        table.insert(blocks, block)
      end
    end
  end

  document.blocks = blocks
  return document
end
