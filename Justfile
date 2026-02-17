PREV := "https://github.com/[a-z-]+/theory/blob/[a-z0-9]+/"
NEXT := "https://anonymous.4open.science/r/2026-itp-artifact-641A/"

copy:
    rsync -av --progress ../theory/* ../theory/.gitignore . \
        --exclude .lake \
        --exclude docbuild \
        --exclude Justfile \
        --exclude README.md \
        --exclude _typos.toml \
        --exclude .vscode/
    cd ../theory/docbuild/ && just
    rsync -av --progress ../theory/docbuild/.lake/build/doc .
    touch doc/.nojekyll
    cd doc && fd --type file --exec sd {{PREV}} {{NEXT}}
