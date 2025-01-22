# ThoR

Alloy5 as embedded DSL in Lean4

## known limitations

- Tabs (\t) are not allowed in Lean source code files. However, existing Alloy specifications may contain such characters. Copying such specifications directly into Lean may lead to problems. This problems can be resolved by replacing all tabs with spaces. This can be done manually or tools like [Tab to Space](https://marketplace.visualstudio.com/items?itemName=TakumiI.tabspace) can be used.
