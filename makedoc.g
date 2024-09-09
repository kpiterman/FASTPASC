LoadPackage( "AutoDoc" );
LoadPackage("FASTPASC");
AutoDoc( rec( scaffold := rec(latex_header_file:="doc/latexhead.tex"),
              autodoc  := rec( files := [ "doc/chapters.autodoc" ])
));
QUIT;

