#!/usr/bin/perl
use strict;
use warnings;

my $file = "../src/NfOrder/doc/NfOrder.text";

my $texfile = "tmp.tex";

my $document = do {
  local $/ = undef;
  open my $fh, "<", $file
    or die "could not open $file: $!";
  <$fh>;
};

#$document =~ s/^\s*\n//mg;

my $rest = $document;

#print $rest;

# get first line
my $firstline;

#print $firstline;

my %stuff;

my $name;

my %functions;

my @subsections;

my $introduction;

my $current_subsection = "none";

my $k = 0;
while ( $rest !~ /^\s*$/s && $k > -1 )
{
  $k = $k + 1;

  $firstline = ( split /\n/, $rest )[0];
  #print "New firstline:$firstline\n";

  if ( $firstline =~ /^\\section/ )
  {
    #print "I found a section\n";
    $rest =~ m/\\section#(.*?)#\n?(.*)/s;
    $name = $1;
    $rest = $2;
    $name =~ s/\n//mg;
    #print "content: $name\n";
    $stuff{name} = $name;
  }
  elsif ( $firstline =~ /^\\introduction/ )
  {
    #print "Found a introduction\n";
    $rest =~ m/\\introduction#(.*?)#\n?(.*)/s;
    $introduction = $1;
    $rest = $2;
    #$introduction =~ s/\n//mg;
    #print "context: $introduction\n";
    $stuff{introduction} = $introduction;
  }
  elsif ( $firstline =~ /^\\subsection/ )
  {
    #print "I found a subsection\n";
    $rest =~ m/\\subsection#(.*?)#\n?(.*)/s;
    $name = $1;
    $rest = $2;
    $name =~ s/\n//mg;
    #print "content: $name\n";
    push @subsections, $name;
    $current_subsection = $name;
    $functions{$current_subsection} = [];
  }

  elsif ( $firstline =~ /^\\function/ )
  {
    #print "Found a function\n";
    if ($rest !~ m/\\function#(.*?)#(.*?)#(.*?)#(.*?)#(.*?)#(.*?)#/)
    {
      #print " proper format\n";
    }

    $rest =~ m/\\function#(.*?)#(.*?)#(.*?)#(.*?)#(.*?)#(.*?)#(.*$)/s;

    my $funname = $1;
    my $sign = $2;
    my $targ = $3;
    my $para = $4;
    my $desc = $5;
    my $exam = $6;
    $rest = $7;

    push @{$functions{$current_subsection}}, [$funname, $sign, $targ, $para, $desc, $exam];

    $rest = $7
  }

  $rest =~ s/^\s*\n//mg;
  #print "restnow:$rest:restend";
  #if ( $rest =~ /^\s*$/s )
  #{
  #  print "rest is empty";
  #}
  #print split /\n/, $rest ;
  #
}

#for (@subsections)
#{
#  print "$_\n";
#  my @o = @{$functions{$_}};
#  my $l = @o;
#
#  print $l;
#  #print $#functions{$_};
#}

print "\\begin{document}\n";
print "\\section{$stuff{name}}\n";
print "\\subsection{Introduction}\n";
print "$introduction\n";

for (@subsections)
{
  print "\\subsection{$_}\n";
  my @k = @{$functions{$_}};
  my $l = @k;
  for (my $i =0; $i < $l; $i++)
  {
      print "\\begin{lstlisting}\n";
      print "$functions{$_}[$i][0]($functions{$_}[$i][1]) -> $functions{$_}[$i][2]\n";
      print "\\end{lstlisting}\n";
      print "\\vspace{-1em}\n";

      if ( $functions{$_}[$i][3] !~ /^\s*$/s )
      {
        print "\\vspace{0em}{\\small\\begin{lstlisting}\n";
        my @ar = split /;/, $functions{$_}[$i][3];
        for (my $j = 0; $j <= $#ar; $j++)
        {
          print "   $ar[$j]\n";
        }
        print "\\end{lstlisting}}\n";
      }

      if ( $functions{$_}[$i][4] !~ /^\s*$/s )
      {
        print "\\desc{";
        print "$functions{$_}[$i][4]}\n";
      }

      if ( $functions{$_}[$i][5] !~ /^\s*$/s )
      {
        print "{\\small \\begin{verbatim}";
        print "$functions{$_}[$i][5]";
        print "\\end{verbatim}}\n";
        print "\\vspace{-2em}\n";
      }
        print "\\hrulefill\n";
      
  }
  #print $l;
  #for ($i = 0; $i <= $k; $i++)
  #{
  #  print $i;
  #}
}
print "\\end{document}\n";
