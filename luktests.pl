use strict;
# This is a regression test for luk.pl and its components.

my $v = 0;
if ($ARGV[0] =~ /[Vv]{1}/) {
	$v = shift (@ARGV);
}

my @testcases = split(/ /,qq(Kpq KNpq KpNq NKpq NKNpq NKpNq KqCKpNpr));
push(@testcases, split(/ /, qq(KKpqr KKNpqr KKpNqr KNKpqr KNKNpqr KNKpNqr)));
push(@testcases, split(/ /, qq(Cpq CNpq CpNq NCpq NCNpq NCpNq)));
push(@testcases, split(/ /, qq(CpCq pCq pqN pqC pCNq NpCq NpCNq NpCNq CrpCNp)));
print join("\n", @testcases), "\n\n";
foreach (@testcases) {
	print qx(perl luk.pl $v $_) if $v;
	print qx(perl luk.pl $_) unless $v;

}
die;
foreach (@testcases) {
	print qx(perl nuwffparse.pl "" $_);
}
die;
foreach (@testcases) {
	print qx(perl typetest.pl $_);
}
die;
foreach (@testcases) {
	print qx(perl parsewfftest.pl $_);
}
die;
