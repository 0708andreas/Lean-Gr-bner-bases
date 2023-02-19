(TeX-add-style-hook
 "project"
 (lambda ()
   (TeX-add-to-alist 'LaTeX-provided-class-options
                     '(("article" "a4paper" "12pt")))
   (TeX-add-to-alist 'LaTeX-provided-package-options
                     '(("inputenc" "utf8") ("fontenc" "T1") ("geometry" "margin=3cm") ("parskip" "skip=10pt") ("csquotes" "autostyle") ("mdframed" "ntheorem") ("ntheorem" "amsmath" "thmmarks" "hyperref") ("cleveref" "capitalize")))
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "path")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "url")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "nolinkurl")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "hyperbaseurl")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "hyperimage")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "hyperref")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "href")
   (add-to-list 'LaTeX-verbatim-macros-with-delims-local "path")
   (TeX-run-style-hooks
    "latex2e"
    "article"
    "art12"
    "inputenc"
    "fontenc"
    "geometry"
    "babel"
    "amssymb"
    "amsmath"
    "ebproof"
    "enumerate"
    "verbatim"
    "xcolor"
    "listings"
    "quiver"
    "parskip"
    "csquotes"
    "kpfonts"
    "inconsolata"
    "hyperref"
    "mdframed"
    "ntheorem"
    "cleveref")
   (TeX-add-symbols
    "N"
    "Z"
    "Q"
    "R"
    "C"
    "dif"
    "Prop"
    "type")
   (LaTeX-add-xcolor-definecolors
    "shadecolor"
    "rulecolor")
   (LaTeX-add-mdframed-mdfdefinestyles
    "thmframed")
   (LaTeX-add-mdframed-mdtheorems
    '("theorem" "new")
    '("proposition" "new")
    '("lemma" "new")
    '("corollary" "new")
    '("definition" "new")
    '("definitionbreak" "new"))
   (LaTeX-add-ntheorem-newtheorems
    "proof")
   (LaTeX-add-ntheorem-newtheoremstyles
    "changedot"
    "changedotbreak"))
 :latex)

