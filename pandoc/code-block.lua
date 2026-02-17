function CodeBlock(elem)
  if #(elem.classes)==0 or elem.classes[1]=='agda' then 
    return pandoc.RawBlock('tex', '\\begin{code}\n' .. elem.text .. '\n\\end{code}')
  else 
    return pandoc.RawBlock('tex', '\\begin{verbatim}\n' .. elem.text .. '\n\\end{verbatim}')
  end
end
