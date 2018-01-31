(TeX-add-style-hook
 "Final_Project_Writeup"
 (lambda ()
   (TeX-add-to-alist 'LaTeX-provided-class-options
                     '(("article" "12pt" "a4paper")))
   (TeX-add-to-alist 'LaTeX-provided-package-options
                     '(("geometry" "left=1in" "bottom=1.5in" "headheight=15pt")))
   (TeX-run-style-hooks
    "latex2e"
    "article"
    "art12"
    "fancyhdr"
    "mathtools"
    "amssymb"
    "array"
    "booktabs"
    "multirow"
    "verbatim"
    "geometry"
    "xcolor"
    "listings"
    "color"
    "hyperref")
   (TeX-add-symbols
    "CC"
    "RR"
    "ZZ"
    "NN"
    "QQ"
    "QC"
    "FF"
    "Tcal"
    "Mcal"
    "Ncal"
    "Ccal"
    "Bcal"
    "e"
    "ve"
    "defeq"
    "eqdef"
    "id"
    "sgn"
    "im"
    "mip"
    "Spl"
    "Gal")))

