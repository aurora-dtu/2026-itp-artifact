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
