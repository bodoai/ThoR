# ThoR

Alloy5 as embedded DSL in Lean4

## known limitations

- Tabs (\t) are not allowed in Lean source code files. However, existing Alloy specifications may contain such characters. Copying such specifications directly into Lean may lead to problems. This problems can be resolved by replacing all tabs with spaces. This can be done manually or tools like [Tab to Space](https://marketplace.visualstudio.com/items?itemName=TakumiI.tabspace) can be used.
- Alloy syntax elements can't be used as identifiers (e.g. pred, fact, assert, ...)

## How to include ThoR in your Project

- Add ThoR as depedency in your lakefile.toml

    ```toml
    [[require]]
    name = "ThoR"
    git = "https://github.com/bodoai/ThoR.git"
    rev = "main"
    ```

    Note, that you can either set rev to main for the latest version or refer to a release (e.g. 0.0.1)
- set your mathlib version to the currently used version of ThoR (see lean-toolchain) and also make sure you use the same lean version in your project to prevent errors
- execute lake update
- clean and build the project

Note that new releases and be created by maintainers (refer to <https://docs.github.com/en/repositories/releasing-projects-on-github/managing-releases-in-a-repository>)
