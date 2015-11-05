# $pdflatex = 'internal custom_latex lualatex %O %S';
$pdf_mode = 1;
$postscript_mode = 0;
$dvi_mode = 0;

$recorder = 1;
$bibtex_use = 2;
$pdf_previewer = "start open %O %S";

add_cus_dep('lagda', 'tex', 0, 'agda_tex');
push @generated_exts, 'agdai';
$clean_ext = '*.agdai';

my $agda_src = "Code.lagda";
my $agda_tex = "Code.tex";
my @agda_flags = ('--allow-unsolved-metas', '--latex', '--latex-dir=.');

sub agda_tex {
    return system('agda', @agda_flags, $agda_src);
}

sub agda_tex_init {
    unless (-e $agda_tex) {
        agda_tex();
    }
}

sub custom_latex {
    agda_tex_init();
    return system @_;
}
