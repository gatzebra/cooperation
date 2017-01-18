use strict;

#	To make this program conform to the requirements of a replacement of the wffparse sub of luk.pl, we need to do the following things:
#	-	accept a string as input and convert it to the array form that we need.
#	-	decide what we want to do about the current $v parameter.
#		It is a global parameter and will have to be handled by luk.pl.
#	-	rework the outputs so that they include the %varref. Keep the reporting outputs so that we have
#		the best of both worlds.

my ($v, $input) = @ARGV;
# my $input = "KNCrNpKKrsCpu";
print "\nTest WFF: $input\n";
my ($flag, $varref, $response, $history) = wffparser($input);
my @response = @{$response};
my %var = %{$varref};

unless ($flag) {
	print "$input is not a WFF.\nIt probably failed on the next character after-->", join('',@response), "\n";
	exit (0);
}
print "$input is a WFF. Congratulations!\n";
my @history = @{$history};
my @table;

print "History:", join(' : ', @history), "\n" if $v;
report("Table", \@table);
#print $flag, "\n\n", join("\n",@response);

sub wffparser {
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
				return(0, \%var, \@history);
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
				return(0, \%var, \@history);
			}
		}
	}
# 	return(1,@parsedwff);
	die "The length of input doesn't match the length of output\n" unless (scalar(@wff) == scalar(@history));
	unless (isnotawff(@wff)) {
			return(1, \%var, \@parsedwff, \@history);
	}
	return(0, \%var, \@parsedwff, \@history);
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

sub isaprim {
	my @inarray = @_;
#	print "isaprim got an array.\n";
	unless (scalar(@inarray) lt 4) {
#		print "isaprim: the array is less than 4\n";
		return 0;
	}
	my $instring = join('',@inarray);
	if (scalar(@inarray) == 1) {
		if ($instring =~ /[pqrst]/) {
			return 1;
		} else {
			return 0;
		}
	} elsif (scalar(@inarray) == 2) {
		if ($instring =~ /^N[pqrst]{1}$/){
			return 1;
		} else {
			return 0;
		}
	} elsif (scalar(@inarray) == 3) {
		if ($instring =~ /^[CAKE]{1}[pqrst]{2}$/){
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
sub isamultiprim {
	my @inarray = @_;
#	print "isaprim got an array.\n";
	unless (scalar(@inarray) lt 4) {
#		print "isaprim: the array is less than 4\n";
		return 0;
	}
	my $instring = join('',@inarray);
	if (scalar(@inarray) == 2) {
		if ($instring =~ /^N[pqrst]{1}$/){
			return 1;
		} else {
			return 0;
		}
	} elsif (scalar(@inarray) == 3) {
		if ($instring =~ /^[CAKE]{1}[pqrst]{2}$/){
			return 1;
		} else {
			return 0;
		}
	}
	return 0;
	
	
}
