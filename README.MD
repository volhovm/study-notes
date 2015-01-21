mathlogic-conspect
==================
It is a branch with the XeLaTeX version of the conspect. How to use it:

```
emacs mathlogic.org
C-c C-e l l
patch -p0 -i change.patch
xelatex mathlogic.tex
xelatex mathlogic.tex # second run to get TOC
?????
PROFIT!
```

TODO:

1. Automatize it better
2. Make it create a better-looking PDF
