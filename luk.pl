# This is LUK. a polish notation propositional calculus parser and evaluator.
# It uses the fact that, in bivalent logic, all logical operators have a normalized expression that uses only N and K.
use strict;

# The first thing we have to do is to parse the input string.
# We accept only WFFs that use these capital letters: CAKEN
# And these lowercase letters: a-z

# So, we have two levels of parse: 
#	does it contain only the permissible letters?
#	does it qualify as a WFF?

# 5-Sep-2015: As I begin to prepare for my first going public with the ideas behind PADI, SemanticMail, and
# MindBook, I want to go through this code and annotate it. 

# First, we check for the verbose flag.
my $v = 0;
if ($ARGV[0] =~ /[Vv]{1}/) {
	$v = 1;
	shift (@ARGV);
}


# Second, we make sure it only contains permissible letters.
print "Got:\t$ARGV[0]\n";
my $expression = &letterparse;

# Now, we make sure that it is a WFF. 
# In addition, we separate out the unique variables and the unique WFF parts.
my ($flag, $varref, $response, $history) = &wffparse($expression);
my %var = %{$varref};
die "There are no vars!\n" unless (%var);
my @response = @{$response};

unless ($flag) {
	print "$expression is not a WFF.\nIt probably failed at the character to the left of-->", join('',@response), "\n\n";
	exit (0);
}
print "$expression is a WFF. Congratulations!\n";
my @history = @{$history};
my @table;

print "History:", join(' : ', @history), "\n" if $v;
#print $flag, "\n\n", join("\n",@response);
my %wffs;

foreach (@table) {
	$wffs{$_} = length($_);
}

# Now, we need to establish a single ordering of the variables so that we have a solid basis for creating the truth tables.
my @orderedvars;

print "\n-----------\nLength\tWFF\n-----------\n";
foreach (sort keys %var) {
	print length($_), "\t$_" , "\n";
	push(@orderedvars, $_);
}
# Similarly for the WFFs, we want to order them by their length because the longer WFFs are compositions of the shorter ones.
my @orderedwffs;
foreach (sort {$wffs{$a}<=>$wffs{$b}} keys %wffs) {
	print $wffs{$_}, "\t", $_, "\n";
	push(@orderedwffs, $_);
}
# We can calculate the number of entries in the truth table because it is a function of the number of variables.
my $truthtablelength = 2**scalar(keys %var);
print "\nColumns in truth table:\t", $truthtablelength, "\n";

# Now,we can create the truth tables for all of the variables because they are interrelated.
my $i =0;
foreach (@orderedvars) {
	my $value = 2**$i;
	my %vhash = ("T" => $value, "F" => $value);
	my @varray;
	@varray = createtruthtable(\%vhash,$truthtablelength/2**($i+1)) ;
	
	$var{$_} = \@varray;
	$i++;
}

print "\n";
foreach (@orderedvars) {
	print join("\, ", @{$var{$_}}),"\t", $_, "\n";
	
# 	print "N$_", "\t", join("\, ", N(@{$var{$_}})),"\n";
# 	my @interim = N(@{$var{$_}});
# 	print "K" . $_ . "N" . $_, "\t", join("\, ", K(\@{$var{$_}},\@interim)),"\n";
}

my $i =0;
for ($i=0; $i<scalar(@orderedwffs);$i++) {
	my @interim;
	if ($orderedwffs[$i] =~ /^[CAKE]/) {
		@interim = cakerules($i,$orderedwffs[$i]);
		$wffs{$orderedwffs[$i]} = \@interim;
		print join("\, ", @{$wffs{$orderedwffs[$i]}}), "\t", $orderedwffs[$i], "\n";
	} else {
		my @interim = logop($orderedwffs[$i]);
		$wffs{$orderedwffs[$i]} = \@interim;
		print join("\, ", @{$wffs{$orderedwffs[$i]}}), "\t", $orderedwffs[$i], "\n";
	}
}

# foreach (@orderedwffs) {
# 	my @interim = logop($_);
# 	$wffs{$_} = \@interim;
# 	print $_, "\t", join("\, ", @{$wffs{$_}}), "\n";
# }
print "\nDone!\n\n";



# SUBROUTINES -------------------------------------------------------------
sub makecmd {
	#	It turns out we can benefit from a translator hash:
	my %tranhash = (
	1	=> "var",
	2	=> "wffs"
	);
	my ($cmdletter, $para1, $para2) = @_;
	my @composition;
	my $outstring;
	push (@composition, $cmdletter);
	if (length($para1) gt 1) {
		push(@composition, "\$" . $tranhash{2} . "\{$para1\}");
	} elsif (length($para1) == 1) {
		push(@composition, "\$" . $tranhash{1} . "\{$para1\}");
	} else {
		die "makecmd: I got an empty 1st parameter!\n";
	}
	if (length($para2) gt 1) {
		push(@composition, "\$" . $tranhash{2} . "\{$para2\}");
	} elsif (length($para2) == 1) {
		push(@composition, "\$" . $tranhash{1} . "\{$para2\}");
	} else {
		die "makecmd: I got an empty 2nd parameter!\n";
	}
	$outstring = $composition[0] . "\(" . $composition[1] . "\," . $composition[2] . "\)";
	return $outstring;
}

sub cakerules {
	my $i = shift;
	my $in = shift;
	my $j;
	my @out;
	my @temp;
	# Get the part that must contain 2 parts
	# The first character must be /CAKE/.
	# The next character binds tightly to the first.
	# Search for all strings that begin with that next character in the truncated wffs hash: %lochash 
	# Then search to see if the other part of the string is also in %lochash.
	#	- if it is, figure out whether to use the %var or %wffs hashes to feed data to the logical operator.
	#	- if it isn't, keep searching.
	#	- if the search is unsuccessful, exit with an error.
	
	
	my %lochash;
	for ($j=0; $j<$i; $j++) {
		$lochash{$orderedwffs[$j]} = length($orderedwffs[$j]);
	}
										# We probably need to add in the %var items.
	for ($j=0; $j<scalar(@orderedvars); $j++) {
		$lochash{$orderedvars[$j]} = length($orderedvars[$j]);
	}
	foreach (keys %lochash) {
		print "\tlochash:\t$_\n" if $v;
	}
	my $logicalop = substr($in,0,1);	# This is the logical operator /CAKE/
	my $remainder = substr($in,1);		# This is the whole rest of the string.
	my $boundchar = substr($in, 1,1);	# This is the character immediately to the right of the operator.
										# We may not need it.
	foreach (sort {length($lochash{$a})<=>length($lochash{$b})} keys %lochash) {
										# The sort ensures we are taking the longest ones first.
		print "cakerules: Looking for $_ in $remainder\n" if $v;
		if ($remainder =~ /^($_)(.+)$/) {
										# This if clause finds the sub-WFF if it is first.
			if (exists $lochash{$2}) {	# This checks to ensure that the other part exists too.
# 				@out = K($var{$1},$var{$2});
									# It would be easiest if we could construct the string and then execute it.
									# I will test that and return with the results. Yes. We use "eval" keyword.
				@out = eval(makecmd($logicalop, $1, $2));
				return @out;
			}
		} elsif ($remainder =~ /^(.+)($_)$/) {
										# This if clause finds the sub-WFF if it is last.
			if (exists $lochash{$1}) {
				@out = eval(makecmd($logicalop, $1, $2));
				return @out;
			}
		}
	}
	die "cakerules: I couldn't find the substrings of $in in the var or wffs hashes!\n";
}

sub logop {
	my $in = shift;
	die "logop got no input: $in\n" unless $in;
	
	# This sub now seems wrongheaded to me.
	# This is essentially reparsing what we have already parsed.
	# The parse pieces must exist in the prior listed items in the array of the foreach loop that feeds this.
	
	# My idea now is to use the previous parse instead of doing a new one.
	# Instead of feeding this sub from a foreach loop and its array elements, let's feed it from a 
	# for loop and its index and the indexed array.
	# Once we are in this sub, we just find the WFFs in the elements prior to the current element
	# That satisfy the parse parts required for the logical operation at hand. 
	# Details, details...
	
	# In fact, we should consider reusing wffparse! At least for the CAKE ops.
	
	my (@temp1, @temp2);
# 	my @in = split(//,$in);
# 	print join("\n", @in);
	my @out;

# The Bare Variable rule
	if ($in =~ /^([a-z]{1})$/) {
		@out = @{$var{$1}};
	}

# The N rules
	if ($in =~ /^N{1}([a-z]{1})$/) {
print "NR1: got $1\n" if ($v);
		@out = N($var{$1});
	} elsif ($in =~ /^N{2}([a-z]{1})$/) {
print "NR2: got $1\n" if ($v);
		@out = @{$var{$1}};
	} elsif ($in =~ /^N{1}(.+)$/) {
print "NR3: got $1\n" if ($v);
		@out = N($wffs{$1});
	} elsif ($in =~ /^N{2}(.+)$/) {
print "NR4: got $1\n" if ($v);
		@out = @{$wffs{$1}};
	} else {
		print "N rules empty for $in\n" if ($v);
	}


# The K rules
# 	if ($in =~ /^K{1}([a-z]{1})([a-z]{1})$/) {
# print "KR1: got $1 and $2\n" if ($v);
# 		@out = K($var{$1},$var{$2});
# 	} elsif ($in =~ /^K{1}([a-z]{1})N([a-z]{1})$/) {
# print "KR2: got $1 and $2\n" if ($v);
# 		@temp1 = N($var{$2});
# 		@out = K($var{$1},\@temp1);
# 	} elsif ($in =~ /^K{1}N([a-z]{1})([a-z]{1})$/) {
# print "KR3: got $1 and $2\n" if ($v);
# 		@temp1 = N($var{$1});
# 		@out = K(\@temp1,$var{$2});
# 	} elsif ($in =~ /^K{1}(.+)([a-z]{1})$/) {
# print "KR4: got $1 and $2\n" if ($v);
# # 		... for KNqCsr
# # 		KR4: got NqCs and r
# 		@out = K($wffs{$1},$var{$2});
# 	} elsif ($in =~ /^K{1}(.+)N([a-z]{1})$/) {
# print "KR5: got $1 and $2\n" if ($v);
# 		@temp1 = N($var{$2});
# 		@out = K($wffs{$1},\@temp1);
# 	} else {
# 		print "K rules empty for $in\n" if ($v);
# 	}


# The C rules
	if ($in =~ /^C{1}([a-z]{1})([a-z]{1})$/) {
print "CR1: got $1 and $2\n" if ($v);
		@out = C($var{$1},$var{$2});
	} elsif ($in =~ /^C{1}(.+)N([a-z]{1})$/) {
print "CR2: got $1 and $2\n" if ($v);
		@temp1 = N($var{$2});
		@out = C($var{$1},\@temp1);
	} elsif ($in =~ /^C{1}N([a-z]{1})([a-z]{1})$/) {
print "CR3: got $1 and $2\n" if ($v);
		@temp1 = N($var{$1});
		@out = C(\@temp1,$var{$2});
	} elsif ($in =~ /^C{1}(.+)([a-z]{1})$/) {
print "CR4: got $1 and $2\n" if ($v);
		@out = C($wffs{$1},$var{$2});
	} elsif ($in =~ /^C{1}(.+)N([a-z]{1})$/) {
print "CR5: got $1 and $2\n" if ($v);
		@temp1 = N($var{$2});
		@out = C($wffs{$1},\@temp1);
	} else {
		print "C rules empty for $in\n" if ($v);
	}


# The Return
	die "The Return: No output!\n" unless @out;
	return @out;
}

sub N {
	my $arrayref = shift;
	my @in = @{$arrayref};
	my %hash = ("T"=>"F","F"=>"T");
	my @out;
	foreach (@in) {
		push(@out, $hash{$_});
	}
	return @out;
}

sub K {
	my $aref1 = shift;
	my $aref2 = shift;
print "K: got $aref1 and $aref2\n" if ($v);
	my @array1 = @{$aref1};
	my @array2 = @{$aref2};
	die "The arrays are not the same size.\n" unless (scalar(@array1)==scalar(@array2));
	my %hash = (
		"TT"=>"T",
		"FF"=>"F",
		"TF"=>"F",
		"FT"=>"F"
		);
	my (@out, $i, $key);
	for ($i=0; $i<scalar(@array1);$i++) {
		$key = $array1[$i] . $array2[$i];
		push(@out, $hash{$key});
	}
	return @out;
	
}

sub C {
	my $aref1 = shift;
	my $aref2 = shift;
print "C: got $aref1 and $aref2\n" if ($v);
	my @array1 = @{$aref1};
	my @array2 = @{$aref2};
	die "The arrays are not the same size.\n" unless (scalar(@array1)==scalar(@array2));
# ECprNKpNr
	my @Nout1 = N($aref2);
	my @Kout = K($aref1, \@Nout1);
	my @out = N(\@Kout);
	return @out;	
}

sub createtruthtable {
	my %hash = %{$_[0]};
	my $multiplier = $_[1];
	my (@output, $i, $j);
	for ($j=0;$j<$multiplier;$j++) {
		foreach(sort keys %hash) {
			for ($i=0; $i<$hash{$_};$i++) {
				push(@output, $_);
			}
		}
	}
	return @output;
}

sub wffparse {
	my (@parsedwff, @history, @revwff, @temp);
	my $input = shift;
	my @wff = split(//,$input);
	my %vars;
	foreach (@wff) {
 		$vars{$_}++ if /[a-z]/;
	}
	@revwff = revarray("wffparser:11",@wff);
	foreach (@revwff) {
		if (/[a-z]/) {
			push(@parsedwff, $_);
			push(@history, $_);
			report ("History",\@history) if $v;
			report ("ParsedWff",\@parsedwff) if $v;
		}
		if (/N/) {
			if (scalar(@parsedwff) gt 0) {
				$temp[0] = pop(@parsedwff);
				$temp[1] = $_ . $temp[0];
				push(@table, $temp[1]);
 				push(@parsedwff, $temp[0]) unless ($temp[0] +~/[a-z]{1}/);
				push(@parsedwff, $temp[1]);
				push(@history, $_);
			report ("History",\@history) if $v;
			report ("ParsedWff",\@parsedwff) if $v;
			} else {
				@history = revarray("wffparser:42",@history) if @history; # If the array is empty don't bother reversing it.
				return(0, \%vars, \@history);
			}
		}
		if (/[CAKE]/) {
			if (scalar(@parsedwff) gt 1) {
				$temp[0] = pop(@parsedwff);
				$temp[1] = pop(@parsedwff);
				$temp[2] = $_ . $temp[0] . $temp[1];
				push(@table, $temp[2]);
 				push(@parsedwff, $temp[1]) unless ($temp[0] +~/[a-z]{1}/);
 				push(@parsedwff, $temp[0]) unless ($temp[0] +~/[a-z]{1}/);
				push(@parsedwff, $temp[2]);
				push(@history, $_);
			report ("History",\@history) if $v;
			report ("ParsedWff",\@parsedwff) if $v;
			} else {
			
				@history = revarray("wffparser:59",@history) if @history; # If the array is empty don't bother reversing it.
				return(0, \%vars, \@history);
			}
		}
	}
# 	return(1,@parsedwff);
	die "The length of input doesn't match the length of output\n" unless (scalar(@wff) == scalar(@history));
	unless (isnotawff(@wff)) {
			return(1, \%vars, \@parsedwff, \@history);
	}
	return(0, \%vars, \@parsedwff, \@history);
}
sub report {
	my ($title, $arrayref) = @_;
	print "-------- $title ----------\n";
	foreach (sort {length($a)<=>length($b)} @{$arrayref}) {
		print "$_\n";
	}
# 	print "\n\t", join("\n\t",@{$arrayref}), "\n";
	
}
sub isnotawff {
	my @inarray = @_;

	# First we get the count of all of the tokens (letters) in the input.
	my $tokencnt = scalar(@inarray);

	# Then we return 0 (false --> it IS a WFF!) if it is a primitive.
	return 0 if isaprim(@inarray);

	# If it doesn't start with one of the capital letters it can't be a WFF: return 1.
	return 1 unless ($inarray[0] =~ /^[CAKEN]{1}$/);

	# If it doesn't end with one of the small letters it can't be a WFF: return 1.
	return 1 unless ($inarray[scalar(@inarray)-1] =~ /^[a-z]{1}$/);

	# Any string prefixed by N must be a WFF.
	if ($inarray[0] eq "N") {
		return 1 if isnotawff(@inarray[1..scalar(@inarray)-1]);
	}
	

	# Now, let's get a count of the CAKEs.
	my ($cakecnt, $ncnt);
	foreach (@inarray) {
		if (/[CAKE]/) {
			$cakecnt++;
		}
	}


	# Now, let's get a count of the Ns.
	foreach (@inarray) {
		if (/N/) {
			$ncnt++;
		}
	}
	
	my $varcnt = $tokencnt - ($cakecnt + $ncnt);
	
	# Finally, here is the equation that must be true if the string is a WFF.
	unless ($varcnt == $cakecnt+1) {
		print "\nRatio rule is violated: $varcnt variables and $cakecnt operators. 
$varcnt is not equal to ", $cakecnt+1, ".\n";
		return 1;
	}
	return 0;	
}


# sub wffparse {
# 	my $expression = shift;
# 	my (@todoqueue, @donequeue, @wffs, $char, $wff, $charcnt, $wffcnt, %truthtable);
# 	@todoqueue = split(//,$expression);
# 	if (isnotawff(@todoqueue)) {
# 		die;
# 	}
# 	my %vars;
# 	foreach (@todoqueue) {
# 		$vars{$_}++ if /[a-z]/;
# 	}
# 	
# #	@todoqueue = revarray(@todoqueue);
# 	$charcnt = 0;
# 	while (@todoqueue) {
# 		$char = pop(@todoqueue);
# 		chomp $char;
# 		$charcnt++;
# 		if ($charcnt == 1) {
# 			if ($char =~ /[a-z]/) {
# 				push(@donequeue, $char);
# 				push(@wffs, $char);
# 			} else {
# 				return 0;
# 			}
# 		} elsif ($charcnt == 2) {
# 			if ($char =~ /[a-z]/) {
# 				push(@donequeue, $char);
# 				push(@wffs, $char);
# 			} elsif ($char =~ /N/) {
# 				push(@donequeue, $char);
# 				$char .= pop(@wffs);
# 				push(@wffs, $char);
# 				$truthtable{$char}=length($char);
# 			} else {
# 				return 0;
# 			}
# 		} else {
# 			if ($char =~ /[a-z]/) {
# 				push(@donequeue, $char);
# 				push(@wffs, $char);
# 			} elsif ($char =~ /N/) {
# 				push(@donequeue, $char);
# 				$char .= pop(@wffs);
# 				push(@wffs, $char);
# 				$truthtable{$char}=length($char);
# 			} elsif ($char =~ /[CAKE]/) {
# 				push(@donequeue, $char);
# 				return 0 if (scalar(@wffs) lt 2);
# 				my ($first, $second, $third);
# 				$first = pop(@wffs);
# 				$second = pop(@wffs);
# 				$third = $char . $first . $second;
# 				push(@wffs, $third);
# 				$truthtable{$third}=length($third);
# 			}
# 		}
# 	}
# 	return (\%vars,\%truthtable);
# }

sub letterparse {
	my $expression = shift @ARGV;
	die "There was no expression given.\n" unless $expression;
#	system(qq(clear));
	if ($expression =~ /^[CAKENa-z]+$/) {
		print "The expression contains only the permitted characters.\n";
		return $expression;
	} else {
		print "Your expression contains one or more letters that are not permitted.\nOnly the following letters are permitted in an expression: CAKENa-z\n";
	}
}
sub isnotawff {
	my @inarray = @_;

	# First we get the count of all of the tokens (letters) in the input.
	my $tokencnt = scalar(@inarray);

	# Then we return 0 (false --> it IS a WFF!) if it is a primitive.
	return 0 if isaprim(@inarray);

	# If it doesn't start with one of the capital letters it can't be a WFF: return 1.
	return 1 unless ($inarray[0] =~ /^[CAKEN]{1}$/);

	# If it doesn't end with one of the small letters it can't be a WFF: return 1.
	return 1 unless ($inarray[scalar(@inarray)-1] =~ /^[a-z]{1}$/);

	# Any string prefixed by N must be a WFF.
	if ($inarray[0] eq "N") {
		return 1 if isnotawff(@inarray[1..scalar(@inarray)-1]);
	}
	

	# Now, let's get a count of the CAKEs.
	my ($cakecnt, $ncnt);
	foreach (@inarray) {
		if (/[CAKE]/) {
			$cakecnt++;
		}
	}


	# Now, let's get a count of the Ns.
	foreach (@inarray) {
		if (/N/) {
			$ncnt++;
		}
	}
	
	my $varcnt = $tokencnt - ($cakecnt + $ncnt);
	
	# Finally, here is the equation that must be true if the string is a WFF.
	unless ($varcnt == $cakecnt+1) {
		print "\nRatio rule is violated: $varcnt variables and $cakecnt operators. 
$varcnt is not equal to ", $cakecnt+1, ".\n";
		return 1;
	}
	return 0;	
}

sub isaprim {
	my @inarray = @_;
#	print "isaprim got an array.\n";
	unless (scalar(@inarray) lt 4) {
#		print "isaprim: the array is less than 4\n";
		return 0;
	}
	my $instring = join('',@inarray);
	if (scalar(@inarray) == 1) {
		if ($instring =~ /[a-z]/) {
			return 1;
		} else {
			return 0;
		}
	} elsif (scalar(@inarray) == 2) {
		if ($instring =~ /^N[a-z]{1}$/){
			return 1;
		} else {
			return 0;
		}
	} elsif (scalar(@inarray) == 3) {
		if ($instring =~ /^[CAKE]{1}[a-z]{2}$/){
			return 1;
		} else {
			return 0;
		}
	}
	return 0;
	
	
}

sub revarray {
	my $callerid = shift;
	my @inarray = @_;
	die "revarray sub was passed an empty array by $callerid.\n" unless (@inarray);
	my @outarray;
	while (@inarray) {
		 push(@outarray, pop(@inarray));
	}
	return @outarray;
}

