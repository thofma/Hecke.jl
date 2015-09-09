#!/usr/bin/perl
use strict;
use warnings;
use Getopt::Long;

my $file = '';
my $make_examples = 0;
my $make_latex = 0;

GetOptions("file=s" => \$file,
          "make-examples" => \$make_examples,
          "make-latex" => \$make_latex);

my $texfile = "tmp.tex";

my $MARKDOWNSYMBOL = "##";

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

my %explanations;

my $name;

my %functions;
my %examples;
my %everything;

my @subsections;

my $introduction;

my $expl;

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
    $rest =~ m/\\section[\w\n]*$MARKDOWNSYMBOL(.*?)$MARKDOWNSYMBOL\n?(.*)/s;
    $name = $1;
    $rest = $2;
    $name =~ s/\n//mg;
    #print "content: $name\n";
    $stuff{name} = $name;
  }
  elsif ( $firstline =~ /^\\introduction/ )
  {
    #print "Found an introduction\n";
    $rest =~ m/\\introduction[\w\n]*$MARKDOWNSYMBOL(.*?)$MARKDOWNSYMBOL\n?(.*)/s;
    $introduction = $1;
    $rest = $2;
    #$introduction =~ s/\n//mg;
    #print "context: $introduction\n";
    $stuff{introduction} = $introduction;
  }
  elsif ( $firstline =~ /^\\subsection/ )
  {
    #print "I found a subsection\n";
    $rest =~ m/\\subsection[\w\n]*$MARKDOWNSYMBOL(.*?)$MARKDOWNSYMBOL(.*?)$MARKDOWNSYMBOL\n?(.*)/s;
    $name = $1;
    $expl = $2;
    $rest = $3;
    $name =~ s/\n//mg;
    #print "content: $name\n";
    push(@subsections, $name);
    $current_subsection = $name;
    $explanations{$name} = $2;
    $functions{$current_subsection} = [];
    $examples{$current_subsection} = [];
    $everything{$current_subsection} = [];
  }
  elsif ( $firstline =~ /^\\randombla/ )
  {
    $rest =~ m/\\randombla[\w\n]*$MARKDOWNSYMBOL(.*?)$MARKDOWNSYMBOL(.*?$)/s;

    my $bla = $1;
    $rest = $2;

    push @{$everything{$current_subsection}}, [ $bla ];
  }

  elsif ( $firstline =~ /^\\function/ )
  {
    ##print "Found a function\n";
    #if ($rest !~ m/\\function[\w\n]*$MARKDOWNSYMBOL(.*?)$MARKDOWNSYMBOL(.*?)$MARKDOWNSYMBOL(.*?)$MARKDOWNSYMBOL(.*?)$MARKDOWNSYMBOL(.*?)$MARKDOWNSYMBOL/)
    #{
    #  #print " proper format\n";
    #}

    $rest =~ m/\\function[\w\n]*$MARKDOWNSYMBOL(.*?)$MARKDOWNSYMBOL(.*?)$MARKDOWNSYMBOL(.*?)$MARKDOWNSYMBOL(.*?)$MARKDOWNSYMBOL(.*?)$MARKDOWNSYMBOL(.*?$)/s;

    my $funname = $1;
    my $sign = $2;
    my $targ = $3;
    my $para = $4;
    my $desc = $5;
    $rest = $6;

#    print "name$funname\n";
#    print "sign:$sign\n";
#    print "targ:$targ\n";
#    print "para:$para\n";
#    print "desc:$desc\n";
#    print "rest:$rest\n";

    push @{$functions{$current_subsection}}, [$funname, $sign, $targ, $para, $desc];
    push @{$everything{$current_subsection}}, [$funname, $sign, $targ, $para, $desc];
  }
  elsif ( $firstline =~ /^\\exam/ )
  {
    #print "Found an example";

    $rest =~ m/\\exam[\w\n]*$MARKDOWNSYMBOL(.*?)$MARKDOWNSYMBOL(.*?)$MARKDOWNSYMBOL\n?(.*)/s;

    my $exam = $1;
    my $prop = $2;
    $rest = $3;

    push @{$examples{$current_subsection}}, [$exam, $prop];
    push @{$everything{$current_subsection}}, [$exam, $prop];
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

#for my $sub (@subsections)
#{
#  print "subsection: $sub\n";
#  #my @o = @{$functions{$_}};
#  #my $l = @o;
#  #print $l;
#
#  my @o = @{$everything{$sub}};
#  my $l = @o;
#  #print $l;
#  print "da: @{$o[1]}\n";
#  print_latex(@{$o[1]});
#
#  #print $#functions{$_};
#}

if ($make_latex eq 1)
{
  print "\\begin{document}\n";
  print "\\section{$stuff{name}}\n";
  print "\\subsection{Introduction}\n";
  print "$introduction\n";

  for my $sub (@subsections)
  {
    print "\\subsection{$sub}\n";
    print "$explanations{$sub}";
    my @k = @{$everything{$sub}};
    my $l = @k;
    for (my $i =0; $i < $l; $i++)
    {
      print_latex(@{$k[$i]});
    }
  }
  print "\\end{document}\n";
}

if ($make_examples eq 1)
{
  print "using hecke;\n";
  for my $sub (@subsections)
  {
    print "#$sub \n";
    my @k = @{$examples{$sub}};
    my $l = @k;
    for (my $i =0; $i < $l; $i++)
    {
      my @exam = @{$k[$i]};
      my $source = $exam[0];
      #print "$source\n";
      my @ar = split(/\n/, $source);
      for my $a (@ar)
      {
        if ($a =~ /julia>/)
        {
          $a =~ s/[ \t]*julia>//g;
          $a =~ s/^\s+//g;
          $a =~ s/ASSERT//g;
          my $b = $a;
          $a =~ s/"/\\"/g;
          print "println(\"julia> $a\")\n";
          print "println(eval(parse(\"$a\")))\n";
        }
      }
      print("\n");
    }
    print("\n");
  }
}

sub print_latex
{
  my $k = @_;

  if ($k eq 5)
  {
    # I have to print a function "
    print "\\begin{lstlisting}\n";
    print "$_[0]($_[1]) -> $_[2]\n";
    print "\\end{lstlisting}\n";
    print "\\vspace{-1em}\n";

    if ( $_[3] !~ /^\s*$/s )
    {
      print "\\vspace{0em}{\\small\\begin{lstlisting}\n";
      my @ar = split /;/, $_[3];
      for (my $j = 0; $j <= $#ar; $j++)
      {
        print "   $ar[$j]\n";
      }
      print "\\end{lstlisting}}\n";
    }

    if ( $_[4] !~ /^\s*$/s )
    {
      print "\\desc{";
      print "$_[4]}\n";
      print "\\vspace{1em}\n";
    }
    # print "\\noindent\\hfil\\rule{0.8\\textwidth}{.4pt}\\hfil";
    # print "\\hrulefill\n";
  }
  if ($k eq 2)
  {
    # I have to print an example 
    if ( $_[0] !~ /^\s*$/s )
    {
      print "\\begin{center}\\rule{0.5\\textwidth}{.4pt}\\end{center}\n";
      print "\\begin{quote}{ \\begin{verbatim}";
      $_[0] =~ s/.*ASSERT.*\n//g;
      print "$_[0]";
      print "\\end{verbatim}}\\end{quote}\n";
      #print "\\vspace{-0.5em}\n";
      print "\\begin{center}\\rule{0.5\\textwidth}{.4pt}\\end{center}\n";
      #print "\\vspace{0.5em}\n";
      #print "\\hrulefill\n";
    }
  }
  if ($k eq 1)
  {
    # I have to print random bla
    #print "\\newline n";
    print "$_[0]\n";
  }
}


