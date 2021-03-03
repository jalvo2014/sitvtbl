#!/usr/local/bin/perl -w
#------------------------------------------------------------------------------
# Licensed Materials - Property of IBM (C) Copyright IBM Corp. 2010, 2010
# All Rights Reserved US Government Users Restricted Rights - Use, duplication
# or disclosure restricted by GSA ADP Schedule Contract with IBM Corp
#------------------------------------------------------------------------------

#  perl sitvtbl.pl
#
#  Create SQL to delete certain Virtual Table UADVISOR Updaters
#
#  john alvord, IBM Corporation, 16 June 2014
#  jalvord@us.ibm.com
#
# tested on Windows Activestate 5.16.2
#
# $DB::single=2;

## todos
#
#  Workflow policy usage
#
#  Display item??
#
#  Use better parse_lst routine

#use warnings::unused; # debug used to check for unused variables
use strict;
use warnings;
use Data::Dumper;               # debug only

# See short history at end of module

my $gVersion = "1.10000";
my $gWin = (-e "C://") ? 1 : 0;    # 1=Windows, 0=Linux/Unix

# communicate without certificates
BEGIN {
   $ENV{'PERL_NET_HTTPS_SSL_SOCKET_CLASS'} = "Net::SSL";
   $ENV{'PERL_LWP_SSL_VERIFY_HOSTNAME'} = 0;
};   #

use Data::Dumper;               # debug only

# following object used to parse SOAP results and xml files.
my $tpp;

# a collection of variables which are used throughout the program.
# defined globally

my $args_start = join(" ",@ARGV);      # capture arguments for later processing
my $soap_rc;                           # return code from DoSoap call
my $soap_faultstr;                     # fault string from SOAP results
my $soap_faultcode;                    # fault code - where the fault originates
my $run_status = 0;                    # A count of pending runtime errors - used to allow multiple error detection before stopping process
my $oHub;                              # SOAP::Lite object to define connection

my %osagentx;
my %vtagentx;
my %agentx;

# some common variables

my @list = ();                         # used to get result of good SOAP capture
my $rc;
my $node;
my $survey_sqls = 0;                     # count of SQLs
my $survey_sql_time = 0;                 # record total elapsed time in SQL processing
my @words = ();
my $rt;
my $debugfile;
my $ll;
my $pcount;
my $oneline;
my $sx;
my @connections = ();                    # list of possible hub TEMS servers
my $connection="";                       # connection chosen to primary hub TEMS
my $key;

my %agentipx;

my $xmli = -1;
my @xmlfile = ();

# forward declarations of subroutines

sub init;                                # read command line and ini file
sub logit;                               # queue one record to survey log
sub DoSoap;                              # perform a SOAP request and return results
sub get_timestamp;                       # get current timestatmp
sub calc_timestamp;                      # Add or subtract time from an ITM timestamp
sub datadumperlog;                       # dump a variable using Dump::Data if installed
sub get_connection;                      # get current connection string
sub gettime;                             # get time
sub get_list;                            # unwind recursive array
sub init_soap;                           # input from Perl/SOAP to hub TEMS
sub init_txt;                            # input from txt files
sub newsit;                              # create new situation entry
sub sitgroup_get_sits;                   # recursive sitgroup exploration
sub new_tnodesav;                        # process the TNODESAV columns

my $tx;
my $temsi = -1;
my @tems = ();
my %temsx = ();
my @tems_online = ();
my @tems_vtbl = ();
my $hub_tems;

my $nsx;
my $nsavei = -1;
my @nsave = ();
my %nsavex = ();
my @nsave_product = ();
my @nsave_o4online = ();
my @nsave_reserved = ();
my @nsave_temaver = ();

my %recyclex = ();

my $siti = -1;                             # count of situations
my @sit = ();                              # situation name
my @sit_autostart = ();                    # situation autostart


# Situation Group related data
my %sum_sits = ();

# Situation related data

my $curi;                                  # global index for subroutines
my %sitx = ();                             # Index from situation name to index


# following situations exhibity SP2OS-ish behavior. This is a very early style where
# a UADVISOR situation is used to keep a in storage virtual table up to date. This fails
# badly when there are many [40+] agents and causes TEMS communication outages. They are
# identified here to alert the user.

my %hSP2OS = (
UADVISOR_OMUNX_SP2OS => "UX",
UADVISOR_KOQ_VKOQDBMIR => "OQ",
UADVISOR_KOQ_VKOQLSDBD => "OQ",
UADVISOR_KOQ_VKOQSRVR => "OQ",
UADVISOR_KOQ_VKOQSRVRE => "OQ",
UADVISOR_KOR_VKORSRVRE => "OR",
UADVISOR_KOR_VKORSTATE => "OR",
UADVISOR_KOY_VKOYSRVR => "OY",
UADVISOR_KOY_VKOYSRVRE => "OY",
UADVISOR_KQ5_VKQ5CLUSUM => "Q5",
UADVISOR_KHV_VKHVHYPERV => "HV",                #KHV.VKHVHYPERV
);

my %suffx = (
               "UX" => ":KUX",
               "OQ" => ":MSS",
               "OR" => ":ORA",                   # a guess - have not seen one. OR replaced with RZ
               "OY" => ":SYB",
               "Q5" => ":Q5",
               "HV" => ":HV",
            );

my %osx = (
             "NT" => 1,
             "LZ" => 1,
             "UX" => 1,
          );

my %vtblx = (
               "UX" => 1,
               "OQ" => 1,
               "OR" => 1,
               "OY" => 1,
               "Q5" => 1,
               "HV" => 1,
            );


# option and ini file variables variables

my $opt_txt;                    # input from .txt files
my $opt_txt_tnodelst;           # TNODELST txt file
my $opt_txt_tnodesav;           # TNODESAV txt file
my $opt_txt_tsitdesc;           # TSITDESC txt file
my $opt_lst;                    # input from .txt files
my $opt_lst_tnodelst;           # TNODELST lst file
my $opt_lst_tnodesav;           # TNODESAV lst file
my $opt_lst_tsitdesc;           # TSITDESC lst file
my $opt_exl;                    # tems exclude
my $opt_gensql;                 # generate needed sql
my $opt_soap;                   # input from hub TEMS via SOAP
my $opt_log;                    # name of log file
my $opt_ini;                    # name of ini file
my $opt_debuglevel;             # Debug level
my $opt_debug;                  # Debug level
my $opt_h;                      # help file
my $opt_v;                      # verbose flag
my $opt_vt;                     # verbose traffic flag
my $opt_dpr;                    # dump data structure flag
my $opt_std;                    # Credentials from standard input
my $opt_soap_timeout;           # How long to wait SOAP request
my $opt_workpath;               # Directory to store output files
my $opt_recycle;                # when one, create recycle files
my $opt_recycle_cmd = "recycle.cmd";
my $opt_recycle_sh  = "recycle.sh";
my $user="";
my $passwd="";

# do basic initialization from parameters, ini file and standard input

$rc = init();

$opt_log = $opt_workpath . $opt_log;
open FH, "+>>$opt_log" or die "can't open $opt_log: $!";

logit(0,"SITAUDIT000I - ITM_virt_table $gVersion $args_start");

# process two different sources of node data

if ($opt_soap == 1) {                   # SOAP
   $rc = init_soap();
} elsif ($opt_txt == 1) {               # text files
   $rc = init_txt();
} elsif ($opt_lst == 1) {               # text files
   $rc = init_lst();
}

my $t;
my $onetems;

# model delete statements  - originally created manually

#DELETE FROM O4SRV.TSITDESC                                 WHERE SITNAME = 'UADVISOR_OMUNX_SP2OS';
#DELETE FROM O4SRV.SITDB                                    WHERE RULENAME = 'OMUNX.SP2OS';
#DELETE FROM O4SRV.SITDB                                    WHERE RULENAME = 'UADVISOR_OMUNX_SP2OS____________';
#
#DELETE FROM O4SRV.TSITDESC AT('REMOTE_armzram001bptxd')    WHERE SITNAME = 'UADVISOR_OMUNX_SP2OS';
#DELETE FROM O4SRV.SITDB AT('REMOTE_armzram001bptxd')       WHERE RULENAME = 'vOMUNX.SP2OS';
#DELETE FROM O4SRV.SITDB AT('REMOTE_armzram001bptxd')       WHERE RULENAME = 'UADVISOR_OMUNX_SP2OS____________';
#
#
#DELETE FROM O4SRV.TSITDESC                                 WHERE SITNAME LIKE 'UADVISOR_KO';
#DELETE FROM O4SRV.SITDB                                    WHERE RULENAME LIKE 'KOQ.VK';
#DELETE FROM O4SRV.SITDB                                    WHERE RULENAME LIKE 'KOY.VK';
#DELETE FROM O4SRV.SITDB                                    WHERE RULENAME WHERE RULENAME LIKE 'UADVISOR_KO';
#
#DELETE FROM O4SRV.TSITDESC AT('REMOTE_armzram001bptxd')    WHERE SITNAME LIKE 'UADVISOR_KO';
#DELETE FROM O4SRV.SITDB AT('REMOTE_armzram001bptxd')       WHERE RULENAME LIKE 'KOQ.VK';
#DELETE FROM O4SRV.SITDB AT('REMOTE_armzram001bptxd')       WHERE RULENAME LIKE 'KOY.VK';
#DELETE FROM O4SRV.SITDB AT('REMOTE_armzram002svexd')       WHERE RULENAME LIKE 'UADVISOR_KO';

my $show_sql = "show.sql";
my $delete_sql = "delete.sql";

open SH, "+>$show_sql" or die "can't open $show_sql: $!";
open DH, "+>$delete_sql" or die "can't open $delete_sql: $!";

my $show_line;
my $delete_line;

for (my $i = 0; $i <= $temsi; $i++) {
   if ($opt_exl ne "") {
      next if index($tems[$i],$opt_exl) != -1;
   }
   next if $tems_vtbl[$i] == 0;
   my $at_tems = "";
   $at_tems = "AT('$tems[$i]')" if $tems[$i] ne $hub_tems;

   print DH "DELETE FROM O4SRV.TSITDESC $at_tems\n";
   print DH "   WHERE SITNAME='UADVISOR_OMUNX_SP2OS';\n";
   print DH "DELETE FROM O4SRV.SITDB $at_tems\n";
   print DH "    WHERE RULENAME LIKE 'UADVISOR_OMUNX_SP2OS';\n";
   print DH "DELETE FROM O4SRV.SITDB $at_tems\n";
   print DH "    WHERE RULENAME='OMUNX.SP2OS';\n";

   print DH "DELETE FROM O4SRV.TSITDESC $at_tems\n";
   print DH "   WHERE SITNAME LIKE 'UADVISOR_KOQ_V';\n";
   print DH "DELETE FROM O4SRV.SITDB $at_tems\n";
   print DH "   WHERE RULENAME LIKE 'UADVISOR_KOQ_V';\n";
   print DH "DELETE FROM O4SRV.SITDB $at_tems\n";
   print DH "   WHERE RULENAME LIKE 'KOQ.V';\n";

   print DH "DELETE FROM O4SRV.TSITDESC $at_tems\n";
   print DH "   WHERE SITNAME LIKE 'UADVISOR_KOR_V';\n";
   print DH "DELETE FROM O4SRV.SITDB $at_tems\n";
   print DH "   WHERE RULENAME LIKE 'UADVISOR_KOR_V';\n";
   print DH "DELETE FROM O4SRV.SITDB $at_tems\n";
   print DH "   WHERE RULENAME LIKE 'KOR.V';\n";

   print DH "DELETE FROM O4SRV.TSITDESC $at_tems\n";
   print DH "   WHERE SITNAME LIKE 'UADVISOR_KOY_V';\n";
   print DH "DELETE FROM O4SRV.SITDB $at_tems\n";
   print DH "   WHERE RULENAME LIKE 'UADVISOR_KOY_V';\n";
   print DH "DELETE FROM O4SRV.SITDB $at_tems\n";
   print DH "   WHERE RULENAME LIKE 'KOY.V';\n";

   print DH "DELETE FROM O4SRV.TSITDESC $at_tems\n";
   print DH "   WHERE SITNAME LIKE 'UADVISOR_KQ5_V';\n";
   print DH "DELETE FROM O4SRV.SITDB $at_tems\n";
   print DH "   WHERE RULENAME LIKE 'UADVISOR_KQ5_V';\n";
   print DH "DELETE FROM O4SRV.SITDB $at_tems\n";
   print DH "   WHERE RULENAME LIKE 'KQ5.V';\n";

   print DH "DELETE FROM O4SRV.TSITDESC $at_tems\n";
   print DH "   WHERE SITNAME LIKE 'UADVISOR_KHV_V';\n";
   print DH "DELETE FROM O4SRV.SITDB $at_tems\n";
   print DH "   WHERE RULENAME LIKE 'UADVISOR_KHV_V';\n";
   print DH "DELETE FROM O4SRV.SITDB $at_tems\n";
   print DH "   WHERE RULENAME LIKE 'KHV.V';\n";


   print SH "SELECT SITNAME FROM O4SRV.TSITDESC $at_tems\n";
   print SH "   WHERE SITNAME='UADVISOR_OMUNX_SP2OS';\n";
   print SH "SELECT RULENAME FROM O4SRV.SITDB $at_tems\n";
   print SH "    WHERE RULENAME LIKE 'UADVISOR_OMUNX_SP2OS';\n";
   print SH "SELECT RULENAME FROM O4SRV.SITDB $at_tems\n";
   print SH "    WHERE RULENAME='OMUNX.SP2OS';\n";

   print SH "SELECT SITNAME FROM O4SRV.TSITDESC $at_tems\n";
   print SH "   WHERE SITNAME LIKE 'UADVISOR_KOQ_V';\n";
   print SH "SELECT RULENAME FROM O4SRV.SITDB $at_tems\n";
   print SH "   WHERE RULENAME LIKE 'UADVISOR_KOQ_V';\n";
   print SH "SELECT RULENAME FROM O4SRV.SITDB $at_tems\n";
   print SH "   WHERE RULENAME LIKE 'KOQ.V';\n";

   print SH "SELECT SITNAME FROM O4SRV.TSITDESC $at_tems\n";
   print SH "   WHERE SITNAME LIKE 'UADVISOR_KOR_V';\n";
   print SH "SELECT RULENAME FROM O4SRV.SITDB $at_tems\n";
   print SH "   WHERE RULENAME LIKE 'UADVISOR_KOR_V';\n";
   print SH "SELECT RULENAME FROM O4SRV.SITDB $at_tems\n";
   print SH "   WHERE RULENAME LIKE 'KOR.V';\n";

   print SH "SELECT SITNAME FROM O4SRV.TSITDESC $at_tems\n";
   print SH "   WHERE SITNAME LIKE 'UADVISOR_KOY_V';\n";
   print SH "SELECT RULENAME FROM O4SRV.SITDB $at_tems\n";
   print SH "   WHERE RULENAME LIKE 'UADVISOR_KOY_V';\n";
   print SH "SELECT RULENAME FROM O4SRV.SITDB $at_tems\n";
   print SH "   WHERE RULENAME LIKE 'KOY.V';\n";

   print SH "SELECT SITNAME FROM O4SRV.TSITDESC $at_tems\n";
   print SH "   WHERE SITNAME LIKE 'UADVISOR_KQ5_V';\n";
   print SH "SELECT RULENAME FROM O4SRV.SITDB $at_tems\n";
   print SH "   WHERE RULENAME LIKE 'UADVISOR_KQ5_V';\n";
   print SH "SELECT RULENAME FROM O4SRV.SITDB $at_tems\n";
   print SH "   WHERE RULENAME LIKE 'KQ5.V';\n";

   print SH "SELECT SITNAME FROM O4SRV.TSITDESC $at_tems\n";
   print SH "   WHERE SITNAME LIKE 'UADVISOR_KHV_V';\n";
   print SH "SELECT RULENAME FROM O4SRV.SITDB $at_tems\n";
   print SH "   WHERE RULENAME LIKE 'UADVISOR_KHV_V';\n";
   print SH "SELECT RULENAME FROM O4SRV.SITDB $at_tems\n";
   print SH "   WHERE RULENAME LIKE 'KHV.V';\n";
}

close SH;
close DH;

# if recycle option, create cmd and sh files to recycle agents involved.
# For non-OS Agents, a tacmd restartAgent will do.
# For UX, an OS Agent, idea is to set a debug environment variable
# to N which is default like this:.
# ./tacmd setagentconnection -t LZ -n NMP180:LZ -e IRA_DUMP_DATA=N

open CMD, "+>$opt_recycle_cmd" or die "can't open $opt_recycle_cmd: $!";
open SH, "+>$opt_recycle_sh" or die "can't open $opt_recycle_sh: $!";
binmode(SH);

my $cmd_line;
for (my $i=0;$i<=$siti;$i++) {
   my $j;
   if (substr($sit[$i],0,8) eq "UADVISOR") {          # scan for particulat Historical UADVISORs
      if ($sit_autostart[$i] ne "*NO") {              ##check maybe ne "*NO" versus *SYN ????
         my $hx = $hSP2OS{$sit[$i]};                  # ignore unless this a virtual hub table update
         next if !defined $hx;
         for ($j=0;$j<=$nsavei;$j++){                 # look through all agents
            my $iproduct = $nsave_product[$j];        # ignore offline agents
            next if $nsave_o4online[$j] ne "Y";
            next if $iproduct ne $hx;                 # ignore if agent product is not the one with UADVISOR
            $DB::single=2 if $nsave[$j] eq "MSSQLSERVER:P8WRCPEBTSQ01B:MSS";
            my $iip = $agentipx{$nsave[$j]};          # see if agent has known IP address
            if (!defined $iip) {
               warn "agent $nsave[$j] has no recorded IP address";
               next;
            }
            my $vtagent_ref = $vtagentx{$iip};        # look up the VT [Virtual Table] agent
            if (!defined $vtagent_ref) {
               warn "vtagentx unknown for ip address $iip";
               next;
            }
            my $vtagenti_ref = $vtagent_ref->{instances}{$nsave[$j]};
            next if !defined $vtagenti_ref;
            $vtagenti_ref->{restart} += 1;             # up agent restart count
            if ($vtagenti_ref->{restart} == 1) {       # only do restart logic once
               # validate the agent name suffix.      # The tacmd restart agent depends on it
               my $isuff = $suffx{$hx};
               my $neglen = -1 * length($isuff);
               if (substr($nsave[$j],$neglen) ne $isuff) { # if missing, emit a warning/info message
                  my $com_line = "System[$iip] Agent[$nsave[$j] - agent name truncated [not ending in $isuff] so manual restart required\n";
                  print CMD "REM " . $com_line;
                  print SH "# " . $com_line;
                  next;
               }
               my $osagent_ref = $osagentx{$iip};     # Check to see if OS Agent is present
               if (defined $osagent_ref) {            # need OS agent
                  if ($osagent_ref->{hostname} eq $vtagenti_ref->{hostname}) {  # do hostnames agree
                     $cmd_line = "tacmd restartAgent -m  $nsave[$j]\n";
                     if ($hx eq "UX") {
                        if ($nsave_temaver[$j] ge "06.23.00") {
                           $cmd_line = "tacmd setagentconnection -t $hx -n $nsave[$j] -e IRA_DUMP_DATA=N\n";
                        } else {
                           my $com_line = "System[$iip] Agent[$nsave[$j] - manual restart required since ITM 622 or earlier\n";
                           print CMD "REM " . $com_line;
                           print SH "# " . $com_line;
                           next;
                        }
                     }
                     print CMD $cmd_line;
                     print SH "./" . $cmd_line;
                  } else {
                     $cmd_line = "System[$iip] Agent[$nsave[$j]] has hostname[$vtagenti_ref->{hostname}] conflicts with OS Agent[$osagent_ref->{node} with hostname[$osagent_ref->{hostname}] so manual restart needed\n";
                     print CMD "REM " . $cmd_line;
                     print SH "# " . $cmd_line;
                  }
               } else {
                  $cmd_line = "System[$iip] Agent[$nsave[$j]] has hostname[$vtagenti_ref->{hostname}] has no online OS agent to perform work so manual restart needed\n";
                  print CMD "REM " . $cmd_line;
                  print SH "# " . $cmd_line;
               }
            }
         }
      }
   }
}

close CMD;
close SH;

exit 0;

sub new_tnodesav {
   my ($inode,$iproduct,$io4online,$ireserved,$ihostaddr) = @_;
   $nsx = $nsavex{$inode};
   if (!defined $nsx) {
      $nsavei++;
      $nsx = $nsavei;
      $nsave[$nsx] = $inode;
      $nsavex{$inode} = $nsx;
      $nsave_product[$nsx] = $iproduct;
      $nsave_o4online[$nsx] = $io4online;
      $nsave_reserved[$nsx] = $ireserved;
      $nsave_temaver[$nsx] = "00.00.00";
      if (length($ireserved) >= 0) {
         my @words;
         @words = split(";",$ireserved);
         # found one agent with RESERVED == A=00:ls3246;;;
         if ($#words > 0) {
            if ($words[1] ne "") {
               @words = split(":",$words[1]);
               $nsave_temaver[$nsx] = substr($words[0],2,8);
            }
         }
      }
   }
   if (defined $vtblx{$iproduct}) {      # a vtbl type agent
      $tems_vtbl[$agentx{$inode}] += 1 if defined $agentx{$inode};
   }
   my $iip = "";
   # calculate the ip address of the agent. Some hostaddrs have port numbers and some not.
   if (index($ihostaddr,"[") != -1) {
      $ihostaddr =~ /:#(\S+)\[(\S*)\]/;
      $iip = $1 if defined $1;                # a $1 does not survive and if or else clause
   } else {
      $ihostaddr =~ /#(\S*)/;
      $iip = $1 if defined $1;
   }
   my $ihostname = "";                       # the calculated hostname based on agent name.
   my $ipc = "";
   my $tnode = $inode;
   $tnode =~ s/[^:]//g;
   my $ncolons = length($tnode);
   my @wnodes = split(":",$inode);
   if ($ncolons == 0) {
      $ihostname = $inode;
   } elsif ($ncolons == 1) {
      $ihostname = $wnodes[0];
      $ipc       = $wnodes[1];
      $ipc = "" if !defined $wnodes[1];
   } elsif ($ncolons == 2) {
      $ihostname = $wnodes[1];
      $ipc       = $wnodes[2];
      $ipc = "" if !defined $wnodes[2];
   } elsif ($ncolons >= 3) {
      $ihostname = $wnodes[2];
      $ipc       = $wnodes[3];
      $ipc = "" if !defined $wnodes[3];
   }
   if ($iip ne "") {
      if (defined $osx{$iproduct}) {  # an OS Agent?
         my $osagent_ref = $osagentx{$iip};
         if (!defined $osagent_ref) {
            my %osagentref = (
                                hostname => $ihostname,
                                node => $inode,
                                o4online => $io4online,
                                count => 0,
                             );
            $osagent_ref = \%osagentref;
            $osagentx{$iip}  = \%osagentref;
         }
         $osagent_ref->{count} += 1;
      }

      if (defined $vtblx{$iproduct}) {
         my $vtagent_ref = $vtagentx{$iip};
         if (!defined $vtagent_ref) {
            my %vtagentref = (
                                instances => {},
                                count => 0,
                             );
            $vtagent_ref = \%vtagentref;
            $vtagentx{$iip}  = \%vtagentref;
         }
         $vtagent_ref->{count} += 1;
         my $vtagenti_ref = $vtagent_ref->{instances}{$inode};
         if (!defined $vtagenti_ref) {
            my %vtagentiref = (
                                 hostname => $ihostname,
                                 node => $inode,
                                 o4online => $io4online,
                                 count => 0,
                                 product => $iproduct,
                                 restart => 0,
                              );
            $vtagenti_ref = \%vtagentiref;
            $vtagent_ref->{instances}{$inode} = \%vtagentiref;
         }
         $vtagenti_ref->{count} += 1;
      }
      $agentipx{$inode} = $iip;
   }
}

sub new_tsitdesc {
   my ($isitname,$iautostart) = @_;
   $sx = $sitx{$isitname};
   if (!defined $sx) {
      $siti += 1;
      $sx = $siti;
      $sit[$siti] = $isitname;
      $sitx{$isitname} = $siti;
      $sit_autostart[$siti] = $iautostart;
   }
}



# following routine gets data from txt files. tems2sql.pl is an internal only program which can
# extract data from a TEMS database file.

sub init_txt {
   my @klst_data;
   my $inode;
   my $inodelist;
   my $inodetype;

   my @ksav_data;
   my $io4online;
   my $iproduct;
   my $ireserved;
   my $ihostaddr;

   my @ksit_data;
   my $isitname;
   my $iautostart;


   open(KLST, "< $opt_txt_tnodelst") || die("Could not open lst $opt_txt_tnodelst\n");
   @klst_data = <KLST>;
   close(KLST);

   # run through the data and figure out the hub TEMS

   $ll = 0;
   foreach $oneline (@klst_data) {
      $ll += 1;
      next if $ll < 5;
      $inode = substr($oneline,0,32);
      $inode =~ s/\s+$//;   #trim trailing whitespace
      $inodelist = substr($oneline,33,32);
      $inodelist =~ s/\s+$//;   #trim trailing whitespace
      $inodetype = "M";
      $inodetype = substr($oneline,66,1) if length($oneline) >= 66;
      next if $inodetype ne "M";
      $hub_tems = $inode if $inodelist eq "*HUB";
      if (($inodelist eq "*HUB") or ($inodelist eq "*ALL_CMS")) {
         $temsi += 1;
         $tx = $temsi;
         $tems[$tx] = $inode;
         $tems_vtbl[$tx] = 0;
         $temsx{$inode} = $tx;
      }
   }

   # go through the TNODELST data and track agents connecting to a TEMS

   $ll = 0;
   foreach $oneline (@klst_data) {
      $ll += 1;
      next if $ll < 5;
      $inode = substr($oneline,0,32);
      $inode =~ s/\s+$//;   #trim trailing whitespace
      $inodelist = substr($oneline,33,32);
      $inodelist =~ s/\s+$//;   #trim trailing whitespace
      $inodetype = "";
      $inodetype = substr($oneline,66,1) if length($oneline) >= 66;
      next if $inodetype ne "V";
      # in this case NODELIST is the agent and NODE is the thrunode
      $tx = $temsx{$inode};
      next if !defined $tx;
      $agentx{$inodelist} = $tx;
   }

   open(KSAV, "< $opt_txt_tnodesav") || die("Could not open TNODESAV $opt_txt_tnodesav\n");
   @ksav_data = <KSAV>;
   close(KSAV);

   # Get data for all TNODESAV records
   $ll = 0;
   foreach $oneline (@ksav_data) {
      $ll += 1;
      next if $ll < 5;
      chop $oneline;
      $oneline .= " " x 800;
      $inode = substr($oneline,0,32);
      $inode =~ s/\s+$//;   #trim trailing whitespace
      $io4online = substr($oneline,33,1);
      $iproduct = substr($oneline,42,2);

      # if offline with no product, ignore - maybe produce advisory later
      $iproduct = substr($oneline,42,2);
      $iproduct =~ s/\s+$//;   #trim trailing whitespace
      if ($io4online eq "N") {
         next if $iproduct eq "";
      }
      $ireserved = substr($oneline,50,64);
      $ireserved =~ s/\s+$//;   #trim trailing whitespace
      $ihostaddr = substr($oneline,115,256);
      $ihostaddr =~ s/\s+$//;   #trim trailing whitespace
      new_tnodesav($inode,$iproduct,$io4online,$ireserved,$ihostaddr);
   }

   open(KSIT, "< $opt_txt_tsitdesc") || die("Could not open TSITDESC $opt_txt_tsitdesc\n");
   @ksit_data = <KSIT>;
   close(KSIT);

   # Get data for all TSITDESC records
   $ll = 0;
   foreach $oneline (@ksit_data) {
      $ll += 1;
      next if $ll < 5;
      chop $oneline;
      $oneline .= " " x 400;
      $isitname = substr($oneline,0,32);
      $isitname =~ s/\s+$//;   #trim trailing whitespace
      $iautostart = substr($oneline,33,4);
      $iautostart =~ s/\s+$//;   #trim trailing whitespace
      new_tsitdesc($isitname,$iautostart);
   }


}

# following routine gets data from lst files generated by KfwSQLClient output.
sub parse_lst {
  my ($lcount,$inline) = @_;            # count of desired chunks and the input line
  my @retlist = ();                     # an array of strings to return
  my $chunk = "";                       # One chunk
  my $oct = 0;                          # output chunk count
  my $rest;                             # the rest of the line to process
  chop($inline);
  $inline =~ /\]\s*(.*)/;               # skip by [NNN]  field
  $rest = " " . $1 . "        ";
  my $lenrest = length($rest);          # length of $rest string
  my $restpos = 0;                      # postion studied in the $rest string
  my $nextpos = 0;                      # floating next position in $rest string

  # at each stage we can identify a field with values
  #         <blank>data<blank>
  # and a blank field
  #         <blank><blank>
  # We allow a single embedded blank as part of the field
  #         data<blank>data
  # for the last field, we allow imbedded blanks and logic not needed
  while ($restpos < $lenrest) {
     if ($oct < $lcount) {
        if (substr($rest,$restpos,2) eq "  ") {               # null string case
           $chunk = "";
           push @retlist, $chunk;                 # record null data chunk
           $restpos += 2;
        } else {
           $nextpos = index($rest," ",$restpos+1);
           if (substr($rest,$nextpos,2) eq "  ") {
              $chunk .= substr($rest,$restpos+1,$nextpos-$restpos-1);
              push @retlist, $chunk;                 # record null data chunk
              $chunk = "";
              $oct += 1;
              $restpos = $nextpos + 1;
           } else {
              $chunk .= substr($rest,$restpos+1,$nextpos-$restpos);
              $restpos = $nextpos;
           }
        }
     } else {
        $chunk = substr($rest,$restpos+1);
        $chunk =~ s/\s+$//;                    # strip trailing blanks
        push @retlist, $chunk;                 # record last data chunk
        last;
     }
  }
  return @retlist;
}

sub init_lst {
   my @klst_data;
   my $inode;
   my $inodelist;
   my $inodetype;

   my @ksav_data;
   my $iproduct;
   my $io4online;
   my $ireserved;
   my $ihostaddr;

   my @ksit_data;
   my $isitname;
   my $iautostart;

   open(KLST, "< $opt_lst_tnodelst") || die("Could not open lst $opt_lst_tnodelst\n");
   @klst_data = <KLST>;
   close(KLST);

   # run through the data and figure out the hub TEMS

   $ll = 0;
   foreach $oneline (@klst_data) {
      $ll += 1;
      next if $ll < 2;
      ($inode,$inodelist,$inodetype) = parse_lst(3,$oneline);
      next if $inodetype ne "M";
      $hub_tems = $inode if $inodelist eq "*HUB";
      if (($inodelist eq "*HUB") or ($inodelist eq "*ALL_CMS")) {
         $temsi += 1;
         $tx = $temsi;
         $tems[$tx] = $inode;
         $tems_vtbl[$tx] = 0;
         $temsx{$inode} = $tx;
      }
   }

   # go through the TNODELST data and track agents connecting to a TEMS

   $ll = 0;
   foreach $oneline (@klst_data) {
      $ll += 1;
      next if $ll < 2;
      ($inode,$inodelist,$inodetype) = parse_lst(3,$oneline);
      next if $inodetype ne "V";
      # in this case NODELIST is the agent and NODE is the thrunode
      $tx = $temsx{$inode};
      next if !defined $tx;
      $agentx{$inodelist} = $tx;
   }

   open(KSAV, "< $opt_lst_tnodesav") || die("Could not open TNODESAV $opt_lst_tnodesav\n");
   @ksav_data = <KSAV>;
   close(KSAV);

   # Get data for all TNODESAV records
   $ll = 0;
   foreach $oneline (@ksav_data) {
      $ll += 1;
      next if substr($oneline,0,1) ne "[";                    # Look for starting point
      chop $oneline;
      # KfwSQLClient /e "SELECT NODE,O4ONLINE,PRODUCT,VERSION,HOSTADDR,RESERVED,THRUNODE,AFFINITIES FROM O4SRV.TNODESAV" >QA1DNSAV.DB.LST
      #[1]  BNSF:TOIFVCTR2PW:VM  Y  VM  06.22.01  ip.spipe:#10.121.54.28[11853]<NM>TOIFVCTR2PW</NM>  A=00:WIX64;C=06.22.09.00:WIX64;G=06.22.09.00:WINNT;  REMOTE_catrste050bnsxa  000100000000000000000000000000000G0003yw0a7
      ($inode,$io4online,$iproduct,$ireserved,$ihostaddr) = parse_lst(5,$oneline);
      $inode =~ s/\s+$//;   #trim trailing whitespace
      $iproduct =~ s/\s+$//;   #trim trailing whitespace
      $io4online =~ s/\s+$//;   #trim trailing whitespace
      $ireserved =~ s/\s+$//;   #trim trailing whitespace
      $ihostaddr =~ s/\s+$//;   #trim trailing whitespace
      new_tnodesav($inode,$iproduct,$io4online,$ireserved,$ihostaddr);
   }

   open(KSIT, "< $opt_lst_tsitdesc") || die("Could not open TSITDESC $opt_lst_tsitdesc\n");
   @ksit_data = <KSIT>;
   close(KSIT);

   # Get data for all TSITDESC records
   $ll = 0;
   foreach $oneline (@ksit_data) {
      $ll += 1;
      next if substr($oneline,0,1) ne "[";                    # Look for starting point
      chop $oneline;
      # KfwSQLClient /e "SELECT SITNAME,AUTOSTART" >QA1CSITF.DB.LST
      ($isitname,$iautostart) = parse_lst(2,$oneline);
      $isitname =~ s/\s+$//;   #trim trailing whitespace
      $iautostart =~ s/\s+$//;   #trim trailing whitespace
      new_tsitdesc($isitname,$iautostart);
   }
}

# following extracts the data from a primary hub TEMS using SOAP
# This is derived from the Agent Health Survey logic

sub init_soap {
require Cwd;                        # avoid some warning messages
require SOAP::Lite;                 # simple SOAP processing. add 'debug' to increase tracing
require HTTP::Request::Common;      #   and HTTP - for SOAP processing
require XML::TreePP;                # parse XML
   $tpp = XML::TreePP->new;


   # Parse control file which contains  operational defaults -
   #

   if ($opt_vt == 1) {
      my $traffic_file = $opt_workpath . "traffic.txt";
      open $debugfile, ">$traffic_file" or die "can't open $traffic_file: $!";
      $debugfile->autoflush(1);
   }


   # SOAP Variables

   # Variables associated directly with SOAP calls and responses
   # CPU and Memory

   my $sSQL;

   # variables for storing Situation Description information from the hub TEMS

   my $sx;

   # try out each SOAP connection, looking for the current FTO hub TEMS primary
   # might be just one of course...

   my $got_connection = 0;
   my $num_connections = $#connections;

   foreach my $c (@connections) {
      #  Convert $connection as supplied by ini file into a connection string usable for soap processing
      #  That might be the string as supplied but might require changes to adapt to ports actually used
      $connection = $c;
      logit(0,"Survey trial of connection $connection");
      $rc = get_connection();
      if ($run_status) {
         logit(0,"Survey trial of connection $connection failed, continue to next");
         $DB::single=2 if $opt_debug == 1;
         $run_status = 0;
         next;
      }
   #   $oHub = SOAP::Lite->proxy($connection,timeout => $opt_soap_timeout);
   #   $oHub = SOAP::Lite->proxy($connection,keep_alive=>1,timeout => $opt_soap_timeout);
      $oHub = SOAP::Lite->proxy($connection,keep_alive=>1);
      $oHub->outputxml('true');
      $oHub->on_fault( sub {});      # pass back all errors


   $oHub->transport->add_handler( request_send => sub {
       return if $opt_vt == 0;
       my $req = shift;
       my $cur_time = time;
       print $debugfile "\n$cur_time === BEGIN HTTP REQUEST ===\n";
       print $debugfile $req->dump();
       print $debugfile "\n$cur_time ===   END HTTP REQUEST ===\n";
       return
     }
   );
   $oHub->transport->add_handler( response_header => sub {
       return if $opt_vt == 0;
       my $cur_time = time;
       my $res = shift;
       print $debugfile "\n$cur_time === BEGIN RESPONSE HDRS ===\n";
       print $debugfile $res->dump();
       print $debugfile "\n$cur_time === END RESPONSE HDRS ===\n";
       return
     }
   );
   $oHub->transport->add_handler( response_data => sub {
       my $res = shift;
       my $cur_time = time;
       if ($opt_vt == 1) {
          my $content_length = length($res->content);
          print $debugfile "\n$cur_time === BEGIN HTTP RESPONSE DATA $content_length ===\n";
          print $debugfile $res->content;
          print $debugfile "\n===   END HTTP RESPONSE DATA ===\n";
       }
   #    if (substr($res->content,-20) eq "</SOAP-ENV:Envelope>") {
   #       die "OK"; # Got whole data, not waiting for server to end the communication channel.
   #    }
   #    return 1; # In other cases make sure the handler is called for subsequent chunks
        return 1; # allow next chunk to come it...

   });

   $oHub->transport->add_handler( response_done => sub {
       my $res = shift;
       return if $opt_vt == 0;
       my $cur_time = time;
       print $debugfile "\n$cur_time === BEGIN HTTP RESPONSE DONE ===\n";
       print $debugfile $res->dump();
       print $debugfile "\n===   END HTTP RESPONSE DONE ===\n";
       return
     }
   );

      logit(0,"Survey trial of connection $connection - determine hub TEMS nodeid");
      $sSQL = "SELECT NODE, THRUNODE, HOSTADDR, VERSION FROM O4SRV.INODESTS WHERE O4ONLINE='Y' AND PRODUCT='EM' AND NODE=THRUNODE";
      @list = DoSoap("CT_Get",$sSQL);
      if ($run_status) {
         $DB::single=2 if $opt_debug == 1;
         $run_status = 0;
         next;
      }
      next if $#list == -1;
      $node = $list[0]-> {NODE};
      $hub_tems = $list[0]-> {NODE};

      if ($num_connections == 0) {
         logit(0,"Skip FTO primary node check - only one soap target");
         $got_connection = 1;
         last;
      }

      # check to see if if TGBLBRKR table is available - present on ITM 622 and later
      logit(0,"Survey trial of connection $connection - check for TGBLBRKR presence");
      $sSQL = "SELECT TABL_NAME FROM SYSTEM.SYSTABLES WHERE TABL_NAME='TGBLBRKR'";
      @list = DoSoap("CT_Get",$sSQL);
      if ($run_status) {
         $DB::single=2 if $opt_debug == 1;
         logit(0,"Survey failure during check for TGBLBRKR presence");
         $run_status = 0;
         next;
      }
      if ($#list == -1) {
         $DB::single=2 if $opt_debug == 1;
         logit(0,"Survey TGBLBRKR is not present so cannot check for FTO hub TEMS primary role");
         last;
      }

      logit(0,"Survey trial of connection $connection - determine hub TEMS nodeid");
      $sSQL = "SELECT NODE, THRUNODE, HOSTADDR, VERSION FROM O4SRV.INODESTS WHERE O4ONLINE='Y' AND PRODUCT='EM' AND NODE=THRUNODE";
      @list = DoSoap("CT_Get",$sSQL);
      if ($run_status) {
         $DB::single=2 if $opt_debug == 1;
         $run_status = 0;
         next;
      }
      next if $#list == -1;
      $node = $list[0]-> {NODE};
      $hub_tems = $list[0]-> {NODE};
      logit(0,"Survey trial of connection $connection TEMS $node - determine if hub TEMS is in primary role");
      $sSQL = "SELECT ADDRESS, ANNOT, ENTRTYPE, PORT, PROTOCOL, ORIGINNODE FROM O4SRV.TGBLBRKR WHERE ENTRTYPE = 1 AND ORIGINNODE = \'$hub_tems\'";
      @list = DoSoap("CT_Get",$sSQL);
      if ($run_status) {
         $DB::single=2 if $opt_debug == 1;
         $run_status = 0;
         next;
      }
      next if $#list == -1;
      logit(0,"Survey trial of connection $connection TEMS $node - has FTO primary role");
      $got_connection = 1;
      last;
   }

   if ($got_connection != 1) {
      logit(0,"Survey - no primary hub TEMS found - ending survey");
      exit 1;
   }

   my $inode;
   my $inodelist;
   my $pcount;

   # get TNODELIST to figure out TEMSes
   $sSQL = "SELECT NODE, NODELIST FROM O4SRV.TNODELST";
   @list = DoSoap("CT_Get",$sSQL);
   if ($run_status) { exit 1;}

   $ll = 0;
   $pcount = $#list+1;
   foreach my $r (@list) {
       my $count = scalar(keys %$r);
       $ll++;
       if ($count < 2) {
          logit(10,"working on TNODELST row $ll of $pcount has $count instead of expected 2 keys") if $opt_v == 1;
          next;
       }
       $inode = $r->{NODE};
       $inode =~ s/\s+$//;   #trim trailing whitespace
       $inodelist = $r->{NODELIST};
       $inodelist =~ s/\s+$//;   #trim trailing whitespace
       if ($inodelist eq "*HUB") {
          $hub_tems = $inode;
       } elsif ($inodelist eq "*ALL_CMS") {
          $temsi += 1;
          $tx = $temsi;
          $tems[$tx] = $inode;
          $temsx{$inode} = $tx;
       }
   }

   # get TNODESAV to figure out involved agents
   my $iproduct;
   my $io4online;
   my $ireserved;
   $sSQL = "SELECT NODE, PRODUCT, O4ONLINE, RESERVED FROM O4SRV.TNODESAV";
   @list = DoSoap("CT_Get",$sSQL);
   if ($run_status) { exit 1;}

   $ll = 0;
   $pcount = $#list+1;
   foreach my $r (@list) {
       my $count = scalar(keys %$r);
       $ll++;
       if ($count < 4) {
          logit(10,"working on TNODESAV row $ll of $pcount has $count instead of expected 4 keys") if $opt_v == 1;
          next;
       }
       $inode = $r->{NODE};
       $inode =~ s/\s+$//;   #trim trailing whitespace
       $iproduct = $r->{PRODUCT};
       $iproduct =~ s/\s+$//;   #trim trailing whitespace
       $io4online = $r->{O4ONLINE};
       $io4online =~ s/\s+$//;   #trim trailing whitespace
       $ireserved = $r->{RESERVED};
       $ireserved =~ s/\s+$//;   #trim trailing whitespace
       new_tnodesav($inode,$iproduct,$io4online,$ireserved);
   }

   # get TSITDESC to figure out situations
   my $isit;
   my $iautostart;
   $sSQL = "SELECT SITNAME, AUTOSTART, FROM O4SRV.TSITDESC";
   @list = DoSoap("CT_Get",$sSQL);
   if ($run_status) { exit 1;}

   $ll = 0;
   $pcount = $#list+1;
   foreach my $r (@list) {
       my $count = scalar(keys %$r);
       $ll++;
       if ($count < 3) {
          logit(10,"working on TSITDESC row $ll of $pcount has $count instead of expected 2 keys") if $opt_v == 1;
          next;
       }
       $isit = $r->{SITNAME};
       $isit =~ s/\s+$//;   #trim trailing whitespace
       $iautostart = $r->{AUTOSTART};
       $iautostart =~ s/\s+$//;   #trim trailing whitespace
       new_tsitdesc($isit,$iautostart);
   }
}


# Get options from command line - first priority
sub init {

   while (@ARGV) {
   if ($ARGV[0] eq "-h") {
      shift(@ARGV);
      $opt_h= 1;
   }
   elsif ($ARGV[0] eq "-log") {
      shift(@ARGV);
      $opt_log = shift(@ARGV);
      die "-log option with no following filename" if !defined $opt_log;
   }
   elsif ($ARGV[0] eq "-ini") {
      shift(@ARGV);
      $opt_ini = shift(@ARGV);
      die "-ini option with no following filename" if !defined $opt_ini;
   }
   elsif ($ARGV[0] eq "-user") {
      shift(@ARGV);
      $user = shift(@ARGV);
      die "-user option with no following user name" if !defined $user;
   }
   elsif ($ARGV[0] eq "-passwd") {
      shift(@ARGV);
      $passwd = shift(@ARGV);
      die "-passwd option with no following password" if !defined $passwd;
   }
   elsif ($ARGV[0] eq "-v") {
      shift(@ARGV);
      $opt_exl = shift(@ARGV);
      die "-v option with no following text" if !defined $opt_exl;
   }
   elsif ($ARGV[0] eq "-debuglevel") {
      shift(@ARGV);
      $opt_debuglevel = shift(@ARGV);
      die "-debuglevel option with no following number" if !defined $opt_debuglevel;
   }
   elsif ($ARGV[0] eq "-debug") {
      shift(@ARGV);
      $opt_debug = 1;
   }
   elsif ($ARGV[0] eq "-v") {
      shift(@ARGV);
      $opt_v = 1;
   }
   elsif ($ARGV[0] eq "-vt") {
      shift(@ARGV);
      $opt_vt = 1;
   }
   elsif ($ARGV[0] eq "-workpath") {
      shift(@ARGV);
      $opt_workpath = shift(@ARGV);
      die "-workpath option with no following path" if !defined $opt_workpath;
   }
   elsif ($ARGV[0] eq "-std") {
      shift(@ARGV);
      $opt_std = 1;
   }
   elsif ($ARGV[0] eq "-txt") {
      shift(@ARGV);
      $opt_txt = 1;
   }
   elsif ($ARGV[0] eq "-lst") {
      shift(@ARGV);
      $opt_lst = 1;
   }
   elsif ($ARGV[0] eq "-recycle") {
      shift(@ARGV);
      $opt_recycle = 1;
   }
   elsif ($ARGV[0] eq "-gensql") {
      shift(@ARGV);
      $opt_gensql = 1;
   }
   else {
      die "unknown option $ARGV[0]";
   }
   }

   # Following are command line only defaults. All others can be set from the ini file

   if (!defined $opt_ini) {$opt_ini = "sitvtbl.ini";}         # default control file if not specified
   if ($opt_h) {&GiveHelp;}  # GiveHelp and exit program
   if (!defined $opt_debuglevel) {$opt_debuglevel=90;}         # debug logging level - low number means fewer messages
   if (!defined $opt_debug) {$opt_debug=0;}                    # debug - turn on rare error cases
   if (!defined $opt_exl) {$opt_exl="";}                       # debug - turn on rare error cases
   if (!defined $opt_recycle) {$opt_recycle=1;}                # create recycle files
   if (defined $opt_gensql) {                                 # generate needed SQL and quit
      open SQ, ">cnodl.sql" or die "can't open cnod.sql: $!";
      print SQ "SELECT NODE,NODELIST FROM O4SRV.TNODELST;\n";
      close SQ;
      exit 0;
   }
   if (defined $opt_txt) {
      $opt_txt_tnodelst = "QA1CNODL.DB.TXT";
      $opt_txt_tnodesav = "QA1DNSAV.DB.TXT";
      $opt_txt_tsitdesc = "QA1CSITF.DB.TXT";
   }
   if (defined $opt_lst) {
      $opt_lst_tnodelst = "QA1CNODL.DB.LST";
      $opt_lst_tnodesav = "QA1DNSAV.DB.LST";
      $opt_lst_tsitdesc = "QA1CSITF.DB.LST";
   }

   # ini control file must be present

   if (-e $opt_ini) {                                      # make sure ini file is present

      open( FILE, "< $opt_ini" ) or die "Cannot open ini file $opt_ini : $!";
      my @ips = <FILE>;
      close FILE;

      # typical ini file scraping. Could be improved by validating parameters

      my $l = 0;
      foreach my $oneline (@ips)
      {
         $l++;
         chomp($oneline);
         next if (substr($oneline,0,1) eq "#");  # skip comment line
         @words = split(" ",$oneline);
         next if $#words == -1;                  # skip blank line
          if ($#words == 0) {                         # single word parameters
            if ($words[0] eq "verbose") {$opt_v = 1;}
            elsif ($words[0] eq "traffic") {$opt_vt = 1;}
            elsif ($words[0] eq "std") {$opt_std = 1;}
            else {
               print STDERR "SITAUDIT003E Control without needed parameters $words[0] - $opt_ini [$l]\n";
               $run_status++;
            }
            next;
         }

         if ($#words == 1) {
            # two word controls - option and value
            if ($words[0] eq "log") {$opt_log = $words[1];}
            elsif ($words[0] eq "user")  {$user = $words[1];}
            elsif ($words[0] eq "passwd")  {$passwd = $words[1];}
            elsif ($words[0] eq "soapurl") {push(@connections,$words[1]);}
            elsif ($words[0] eq "soap") {$opt_soap = 1; push(@connections,$words[1]);}
            elsif ($words[0] eq "log") {$opt_log = $words[1];}
            elsif ($words[0] eq "workpath") {$opt_workpath = $words[1];}
            elsif ($words[0] eq "soap_timeout") {$opt_soap_timeout = $words[1];}
            else {
               print STDERR "SITAUDIT005E ini file $l - unknown control oneline\n"; # kill process after current phase
               $run_status++;
            }
            next;
         }
         if ($#words == 3) {
            # four+ word controls - option and three values and optional message template
            if ($words[0] eq "txt") {
               $opt_txt=1;
               $opt_txt_tnodelst=$words[1];
            } elsif ($words[0] eq "lst") {
               $opt_lst=1;
               $opt_lst_tnodelst=$words[1];
            } else {
               print STDERR "SITAUDIT005E ini file $l - unknown control $oneline\n"; # kill process after current phase
               $run_status++;
            }
            next;
         }
         print STDERR "SITAUDIT005E ini file $l - unknown control $oneline\n"; # kill process after current phase
         $run_status++;
      }
   }

   # defaults for options not set otherwise

   if (!defined $opt_log) {$opt_log = "sitvtbl.log";}           # default log file if not specified
   if (!defined $opt_h) {$opt_h=0;}                            # help flag
   if (!defined $opt_v) {$opt_v=0;}                            # verbose flag
   if (!defined $opt_vt) {$opt_vt=0;}                          # verbose traffic default off
   if (!defined $opt_dpr) {$opt_dpr=0;}                        # data dump flag
   if (!defined $opt_std) {$opt_std=0;}                        # default - no credentials in stdin
   if (!defined $opt_soap_timeout) {$opt_soap_timeout=180;}    # default 180 seconds
   if (!defined $opt_workpath) {$opt_workpath="";}             # default is current directory
   if (!defined $opt_txt) {$opt_txt = 0;}                      # default no txt input
   if (!defined $opt_lst) {$opt_lst = 0;}                      # default no txt input
   if (!defined $opt_soap) {$opt_soap = 0;}                    # default no soap input

   $opt_workpath =~ s/\\/\//g;                                 # convert to standard perl forward slashes
   if ($opt_workpath ne "") {
      $opt_workpath .= "\/" if substr($opt_workpath,length($opt_workpath)-1,1) ne "\/";
   }


   if ($opt_dpr == 1) {
#     my $module = "Data::Dumper";
#     eval {load $module};
#     if ($@) {
#        print STDERR "Cannot load Data::Dumper - ignoring -dpr option\n";
#        $opt_dpr = 0;
#     }
      $opt_dpr = 0;
   }

   # if credential as passed in via standard input, then that takes precendence.

   if ($opt_std == 1) {
      my $stdline = <STDIN>;
      if (defined $stdline) {
         my @values = split(" ",$stdline);
         while (@values) {
            if ($values[0] eq "-user")  {
               shift(@values);
               $user = shift(@values);
               die "STD option -user with no following value\n" if !defined $user;
            } elsif ($values[0] eq "-passwd")  {
               shift(@values);
               $passwd = shift(@values);
               die "STD option -passwd with no following value\n" if !defined $passwd;
            } else {
               my $rest_stdin = join(" ",@values);
               die "unknown option(s) in stdin [$rest_stdin]\n" if defined $rest_stdin;
            }
         }
      }
   }

   # complain about options which must be present
   if (($opt_txt + $opt_lst + $opt_soap) != 1) {
      print STDERR "SITAUDIT006E exactly one of txt/lst/soap must be present\n";
      $run_status++;
   }
   if ($opt_soap == 1) {
      if ($#connections == -1) {
         print STDERR "SITAUDIT006E connection missing in ini file $opt_ini\n";
         $run_status++;
      }
      if ($user eq "") {
         print STDERR "SITAUDIT007E user missing in ini file $opt_ini or stdin\n";
         $run_status++;
      }
   }

   # if any errors, then dump log and exit
   # this way we can show multiple errors at startup
   if ($run_status) { exit 1;}

}


#------------------------------------------------------------------------------
# Perform soap process
#------------------------------------------------------------------------------
sub DoSoap
{
   $survey_sqls++;                             # keep count of SQLs
   $soap_faultstr = "";                             # reset fault string to null
   $soap_faultcode = "";                            # reset fault code to null
   my @results2;
   my $sql_start_time = time;
   my $mySQL;
   my $get_raw;
   my $res;
   my $result;

   my $soap_action = shift;
   if ($soap_action eq "CT_Get") {
      $mySQL = shift;

      my @aParms = (
         SOAP::Data->name(userid => $user ),
         SOAP::Data->name(password => $passwd ),
         SOAP::Data->name(table => 'O4SRV.UTCTIME' ),
         SOAP::Data->name(sql => $mySQL )
      );

      logit(10,"SOAP CT_Get start - $mySQL");
      $res = $oHub->CT_Get(@aParms);
      $soap_rc = $?;
      $survey_sql_time += time - $sql_start_time;
      logit(10,"SOAP CT_Get end [$soap_rc] - $mySQL");

   } elsif ($soap_action eq "CT_Get_Object") {
      $mySQL = shift;
      $get_raw = shift;
      $get_raw = "" if !defined $get_raw;

      my @aParms = (
         SOAP::Data->name(userid => $user ),
         SOAP::Data->name(password => $passwd ),
         SOAP::Data->name(object => $mySQL )
      );

      logit(10,"SOAP CT_Get_Object start - $mySQL");
      $res = $oHub->CT_Get(@aParms);
      $soap_rc = $?;
      $survey_sql_time += time - $sql_start_time;
#     sleep 10;
      logit(10,"SOAP CT_Get_Object end [$soap_rc] - $mySQL");
      return $res if $get_raw eq 'raw';                 # use raw return

   } elsif ($soap_action eq "CT_Alert") {
      my $myAlert_name = shift;
      my $myAlert_source = shift;
      my $myAlert_item = shift;
      my $myAlert_timestamp = shift;

      my @aParms = (
         SOAP::Data->name(table => 'O4SRV.CLACTLCLO4SRV.UTCTIME' ),
         SOAP::Data->name(userid => $user ),
         SOAP::Data->name(password => $passwd ),
         SOAP::Data->name(name =>      $myAlert_name),
         SOAP::Data->name(source =>    $myAlert_source),
         SOAP::Data->name(item =>      $myAlert_item),
         SOAP::Data->name(timestamp => $myAlert_timestamp),
         SOAP::Data->name(results =>   '~')
      );

      logit(10,"SOAP Alert start - $myAlert_name $myAlert_source $myAlert_item $myAlert_timestamp");
      $res = $oHub->CT_Alert(@aParms);
      $soap_rc = $?;
      logit(10,"SOAP Alert end [$soap_rc]");

   } elsif ($soap_action eq "CT_Reset") {
      my $myAlert_name = shift;
      my $myAlert_source = shift;
      my $myAlert_item = shift;
      my $myAlert_timestamp = shift;

      my @aParms = (
         SOAP::Data->name(userid => $user ),
         SOAP::Data->name(password => $passwd ),
         SOAP::Data->name(name =>      $myAlert_name),
         SOAP::Data->name(source =>    $myAlert_source),
         SOAP::Data->name(item =>      $myAlert_item),
         SOAP::Data->name(timestamp => $myAlert_timestamp),
         SOAP::Data->name(results =>   '~')
      );

      logit(10,"SOAP Reset start - $myAlert_name $myAlert_source $myAlert_item $myAlert_timestamp");
      $res = $oHub->CT_Reset(@aParms);
      $soap_rc = $?;
      #$survey_sql_time += time - $sql_start_time;
      logit(10,"SOAP Reset end [$soap_rc]");

   } elsif ($soap_action eq "CT_WTO") {
      my $myAlert_data = shift;
      my $myAlert_severity = shift;
      my $myAlert_category = shift;

      my @aParms = (
         SOAP::Data->name(userid => $user ),
         SOAP::Data->name(password => $passwd ),
         SOAP::Data->name(table => "O4SRV.CLACTLCL" ),
         SOAP::Data->name(object => "Local_System_Command" ),
         SOAP::Data->name(data =>      $myAlert_data),
         SOAP::Data->name(category =>    $myAlert_category),
         SOAP::Data->name(severity =>      $myAlert_severity)
      );

      logit(10,"SOAP WTO start - $myAlert_data $myAlert_category $myAlert_severity");
      $res = $oHub->CT_WTO(@aParms);
      $soap_rc = $?;
      #$survey_sql_time += time - $sql_start_time;
      logit(10,"SOAP CT_WTO end [$soap_rc]");

   } else {
      logit(0,"Unknown SOAP message [$soap_action]");
      exit 1;
  }

if ($soap_rc != 0) {
   # note this possible message "read timeout at C:/Perl/site/lib/LWP/Protocol/http.pm line 433."
   # for timeout cases. Possibly want to retry at some point.
   $soap_faultstr = chop($res);
   logit(0,"ERROR $soap_rc Problem submitting SOAP Call - $soap_faultstr");
   $run_status++;
   return @results2;
}
if (substr($res,0,1) ne "<") {
   $soap_faultstr = $res;
   logit(0,"ERROR $soap_rc SOAP Failure - $soap_faultstr");
   $run_status++;
   return @results2;
}

if (substr($res,0,6) eq "<HTML>") {
   $soap_faultstr = $res;
   logit(0,"ERROR $soap_rc non-SOAP response - $soap_faultstr");
   $run_status++;
   return @results2;
}

#  print STDERR "INFO" . "SOAP Call submitted successfully\n";
if (91 <= $opt_debuglevel) {
   logit(91,"INFO result res[$res]");
}

if ($opt_dpr == 1) {
   if (91 <= $opt_debuglevel) {
      datadumperlog("Data:Dumper of \$res","$res");
   }
}

#

# the eval is needed to trap some illegal soap syntax and save for later analysis
eval {$result = $tpp->parse($res);};
if ($@) {
   $soap_faultstr = $@;
   logit(0,"ERROR syntax error detected by XML::Simple in the XMLin() routine");
   logit(0,"$@");
   logit(0,"INFO result res[$res]");
   $run_status++;
   return @results2;
}

if ($opt_dpr == 1) {
   if (91 <= $opt_debuglevel) {
      datadumperlog("Data:Dumper of \$result","\$result");
   }
}

# Check for an error fault return. Call out a login failure immediately.
# pretty much any error here prevents data retrieval, stop trying

$rt = ref($result->{'SOAP-ENV:Envelope'}->{'SOAP-ENV:Body'}->{'SOAP-ENV:Fault'});
if ($rt eq "HASH") {
      $soap_faultstr = $result->{'SOAP-ENV:Envelope'}->{'SOAP-ENV:Body'}->{'SOAP-ENV:Fault'}->{'faultstring'};
      $soap_faultcode = $result->{'SOAP-ENV:Envelope'}->{'SOAP-ENV:Body'}->{'SOAP-ENV:Fault'}->{'faultcode'};
      logit(0,"ERROR SOAP - $soap_faultcode $soap_faultstr");
      if ($soap_faultstr eq "CMS logon validation failed.") {
         die "Logon userid/password invalid, please correct" if $soap_faultstr eq "CMS logon validation failed.";
      }
      $run_status++;
} else {
   if ($soap_action eq "CT_Get_Object") {
     if ($result->{'SOAP-ENV:Envelope'}->{'SOAP-ENV:Body'}->{'SOAP-CHK:Success'}->{TABLE}->{'OBJECT'} eq "Local_System_Command") {
         return @results2;
     }
   }
   $rt = ref($result->{'SOAP-ENV:Envelope'}->{'SOAP-ENV:Body'}->{'SOAP-CHK:Success'}->{TABLE}->{DATA}->{ROW});                                       #
   if ($rt eq "ARRAY") {
      @results2=@{$result->{'SOAP-ENV:Envelope'}->{'SOAP-ENV:Body'}->{'SOAP-CHK:Success'}->{TABLE}->{DATA}->{ROW}};
   }
   elsif ($rt eq "HASH") {
       push(@results2,$result->{'SOAP-ENV:Envelope'}->{'SOAP-ENV:Body'}->{'SOAP-CHK:Success'}->{TABLE}->{DATA}->{ROW});
   }
   else {       # check if data contained in an envelope
      $rt = ref($result->{'SOAP-ENV:Envelope'}->{'SOAP-ENV:Body'}->{'SOAP-CHK:Success'}->{TABLE}->{DATA}->{ROW});                                       #
      if ($rt eq "ARRAY") {
         @results2=@{$result->{'SOAP-ENV:Envelope'}->{'SOAP-ENV:Body'}->{'SOAP-CHK:Success'}->{TABLE}->{DATA}->{ROW}};
      }
      elsif ($rt eq "HASH") {
         push(@results2,$result->{'SOAP-ENV:Envelope'}->{'SOAP-ENV:Body'}->{'SOAP-CHK:Success'}->{TABLE}->{DATA}->{ROW});
      } else {
         $soap_faultstr = $res;
         logit(0,"ERROR SOAP no data  - $soap_faultstr");
         logit(0,"unknown result type [$rt] processing SOAP Call for $mySQL - missing data");
      }
   }
}

if ($opt_dpr == 1) {
   if (91 <= $opt_debuglevel) {
      datadumperlog("Data:Dumper of \@results2","\@results2");
   }
}

return @results2;
}

#------------------------------------------------------------------------------
sub GiveHelp
{
  $0 =~ s|(.*)/([^/]*)|$2|;
  print <<"EndOFHelp";

  $0 v$gVersion

  This script surveys an ITM environment looking for possibly unhealthy agents
  which are online not responsive.

  Default values:
    log           : sitvtbl.log
    ini           : sitvtbl.ini
    user          : <none>
    passwd        : <none>
    debuglevel    : 90 [considerable number of messages]
    debug         : 0  when 1 some breakpoints are enabled]
    h             : 0  display help information
    v             : 0  display log messages on console
    vt            : 0  record http traffic on traffic.txt file
    dpr           : 0  dump data structure if Dump::Data installed
    std           : 0  get user/password from stardard input

  Example invovation
    $0  -ini <control file> -pc ux

  Note: $0 uses an initialization file [default sitvtbl.ini] for many controls.

EndOFHelp
exit;
}


#------------------------------------------------------------------------------
# capture log record
sub logit
{
   my $level = shift;
   if ($level <= $opt_debuglevel) {
      my $iline = shift;
      my $itime = gettime();
      chop($itime);
      my $oline = $itime . " " . $level . " " . $iline;
      if ($opt_debuglevel >= 100) {
         my $ofile = (caller(0))[1];
         my $olino = (caller(0))[2];
         if (defined $ofile) {
            $oline = $ofile . ":" . $olino . " " . $oline;
         }
      }
      print FH "$oline\n";
      print "$oline\n" if $opt_v == 1;
   }
}

#------------------------------------------------------------------------------
# capture agent log record
#------------------------------------------------------------------------------
# capture agent error record

# write output log
sub datadumperlog
{
   require Data::Dumper;
   my $dd_msg = shift;
   my $dd_var = shift;
   print FH "$dd_msg\n";
   no strict;
   print FH Data::Dumper->Dumper($dd_var);
}

# return timestamp
sub gettime
{
   my $sec;
   my $min;
   my $hour;
   my $mday;
   my $mon;
   my $year;
   my $wday;
   my $yday;
   my $isdst;
   ($sec,$min,$hour,$mday,$mon,$year,$wday,$yday,$isdst)=localtime(time);
   return sprintf "%4d-%02d-%02d %02d:%02d:%02d\n",$year+1900,$mon+1,$mday,$hour,$min,$sec;
}

# get current time in ITM standard timestamp form
sub get_timestamp {
   my $sec;
   my $min;
   my $hour;
   my $mday;
   my $mon;
   my $year;
   my $wday;
   my $yday;
   my $isdst;

   ($sec,$min,$hour,$mday,$mon,$year,$wday,$yday,$isdst)=localtime(time);
   $year += 1900;
   $mon += 1;


   my $nyy = substr("00" . $year,-2,2);
   my $nmo = substr("00" . $mon,-2,2);
   my $ndd = substr("00" . $mday,-2,2);
   my $nhh = substr("00" . $hour,-2,2);
   my $nmm = substr("00" . $min,-2,2);
   my $nss = substr("00" . $sec,-2,2);

   my $etime = "1" . $nyy . $nmo . $ndd . $nhh . $nmm . $nss . "000";  # check time in ITM 16 byte format
   return $etime;
}

# Following logic replicates most of the tacmd processing logic to determine the
# protocol and port number required to access ITM Web Services or SOAP. For input
# it uses the soapurl supplied by the user. From this the following is discovered
#   1) Is a forced protocol supplied  - https or http
#   2) Is a port number supplied
# The natural SOAP URL will be accessed using a remote command with no content. That will verify the userid and password.
# If an error results, then the index.xml file is retrieved and parsed to determine if there is a better port to use
# There are various error conditions that can result and will cause a failure. The most common case
# is be a TEMS behind a firewall that only allows port 3661 access. If the hub TEMS is recycled, the SOAP access
# port would be an ephemeral one. The port number could be discovered in the index.xml data but access would fail.
# In any case, an error message will show what needs to be done.

# SOAP::Lite does not support http6 or https6 at the current level and so that processing is present but
# blocked at present.

sub get_connection {
my $opt_soap_lite_v6 = 0;            # Change to 1 when SOAP::Lite supports http6 and https6
                                     # This allows the support for http6/https6 to be present but not effect processing
my $connect_protocolGiven = 0;       # when 1, soapurl contains a known protocol
my $connect_portGiven = 0;           # when 1, soapurl contains a port number
my $connect_attempthttps = 0;        # when 1, attempt access by https
my $connect_attempthttps6 = 0;       # when 1, attempt access by https6 [ future SOAP::Lite ]
my $connect_attempthttp = 0;         # when 1, attempt access by http
my $connect_attempthttp6 = 0;        # when 1, attempt access by http6  [ future SOAP::Lite ]
my $connect_httpPortNo = "";         # http port number found in index.xml results
my $connect_httpsPortNo = "";        # https port number found in index.xml results
my $connect_ip6PortNo = "";          # http6 port number found in index.xml results   [ future SOAP::Lite ]
my $connect_ips6PortNo = "";         # https6 port number found in index.xml results  [ future SOAP::Lite ]
my $connect_rest;                    # section of soapurl with protocol removed
my $connect_hostName;                # section of soapurl identified as hostname [or ip address] of the server running hub TEMS
my $connect_port;                    # port used to access SOAP server
my $connect_protocol;                # protocol used to access SOAP
my $connect_res;                     # results returned from SOAP
my $test_connection;                 # trial connection string
my $connect_httpsFound;              # during index.xml analysis, https port found
my $connect_httpFound;               # during index.xml analysis, http port found
my $connect_https6Found;             # during index.xml analysis, https6 port found [ future SOAP::Lite ]
my $connect_http6Found;              # during index.xml analysis, http6 port found  [ future SOAP::Lite ]
my $result;
my @results3;                        # array used in parsing top level index.xml results
my @results4;                        # array used in parsing second level index.xml results
my $in_protocol;                     # protocol from index.xml results

   logit(0,"Determine proper SOAP connection based on [$connection]");

   # stage 1, analyze the given connection string

   if (substr($connection,0,8) eq "https://") {                           # user supplied https
      $connect_protocol = "https";
      $connect_attempthttps = 1;
      $connect_attempthttps6 = 1 if $opt_soap_lite_v6 == 1;
      $connect_protocolGiven = 1;
      $connect_rest = substr($connection,8);

   } elsif (substr($connection,0,9) eq "https6://") {                     # user supplied https6, future SOAP::Lite logic
      $DB::single=2 if $opt_debug == 1;
      next unless $opt_soap_lite_v6 == 1;
      $connect_protocol = "https6";
      $connect_attempthttps6 = 1;
      $connect_protocolGiven = 1;
      $connect_rest = substr($connection,9);

   } elsif (substr($connection,0,7) eq "http://") {                       # user supplied http
      $connect_protocol = "http";
      $connect_attempthttp = 1;
      $connect_attempthttp6 = 1 if $opt_soap_lite_v6 == 1;
      $connect_protocolGiven = 1;
      $connect_rest = substr($connection,7);

   } elsif (substr($connection,0,8) eq "http6://") {                      # user supplied http6, future SOAP::Lite logic
      $DB::single=2 if $opt_debug == 1;
      next unless $opt_soap_lite_v6 == 1;
      $connect_protocol = "http6";
      $connect_attempthttp6 = 1;
      $connect_protocolGiven = 1;
      $connect_rest = substr($connection,8);

   } else {
      $connect_attempthttps = 1;                                          # user did not supply protocol, try https and then http
      $connect_attempthttps6 = 1 if $opt_soap_lite_v6 == 1;
      $connect_attempthttp = 1;
      $connect_attempthttp6 = 1 if $opt_soap_lite_v6 == 1;
      $connect_rest = $connection;
   }

   # Stage 2, get the port number if one supplied
   if (index($connect_rest,':') != -1) {
      $connect_rest =~ m/(\S+):(\d+)/;
      $connect_hostName = $1;
      $connect_port = $2;
      $connect_portGiven = 1;
   } else {
      $connect_hostName = $connect_rest;
      $connect_port = "";
   }

   # stage 3, if port number was given but not protocol
   #           if port is associated with protocol then select that protocol
   #           otherwise try https and then http

   if (($connect_port ne "") and  ($connect_protocolGiven == 0)) {
      if ($connect_port == 3661) {
         $connect_attempthttp = 0;
         $connect_attempthttps = 1;
         $connect_attempthttps6 = 1 if $opt_soap_lite_v6 == 1;

      } elsif ($connect_port == 1920) {
         $connect_attempthttp = 1;
         $connect_attempthttps = 0;
         $connect_attempthttp6 = 1 if $opt_soap_lite_v6 == 1;

      } else {
         $connect_attempthttps = 1;
         $connect_attempthttps6 = 1 if $opt_soap_lite_v6 == 1;
         $connect_attempthttp = 1;
         $connect_attempthttp6 = 1 if $opt_soap_lite_v6 == 1;
      }
   }

   # Stage 4 create trial connection string based on attempt settings

   for (my $i=0; $i < 4; $i++) {
      if (($i == 0) and ($connect_attempthttps == 1)) {
         $connect_protocol = 'https' if $connect_protocolGiven == 0;
         $connect_port = '3661' if $connect_portGiven == 0;
      } elsif (($i == 1) and ($connect_attempthttps6 == 1)) {
         $DB::single=2 if $opt_debug == 1;
         $connect_protocol = 'https6' if $connect_protocolGiven == 0;
         $connect_port = '3661' if $connect_portGiven == 0;
      } elsif (($i == 2) and ($connect_attempthttp == 1)) {
         $connect_protocol = 'http' if $connect_protocolGiven == 0;
         $connect_port = '1920' if $connect_portGiven == 0;
      } elsif (($i == 3) and ($connect_attempthttp6 == 1)) {
         $DB::single=2 if $opt_debug == 1;
         $connect_protocol = 'https6' if $connect_protocolGiven == 0;
         $connect_protocol = 'http6' if $connect_protocolGiven == 0;
         $connect_port = '1920' if $connect_portGiven == 0;
      } else {
         next;
      }
      $test_connection = $connect_protocol . "://" . $connect_hostName . ":" . $connect_port . "///cms/soap";
      logit(0,"Trial SOAP connection based on [$test_connection]");
      $oHub = SOAP::Lite->proxy($test_connection,timeout => $opt_soap_timeout);          # set Soap::Lite controls
      $oHub->outputxml('true');                                                               # require xml output
      $oHub->on_fault( sub {});      # pass back all errors                                   # pass back error conditions
      $connect_res = DoSoap('CT_Get_Object','Local_System_Command');                          # attempt connection
      $run_status = 0;                                                                        # reset failure counter, since only resting
      if ($soap_rc == 0) {                                                                         # if good return code and empty fault string, then declare success
         if ($soap_faultstr eq "") {
            logit(0,"SOAP connection success [$test_connection]");
            $connection = $test_connection;
            return 0;
         }
      }

      # Prior to ITM 6.2, there was different logic. At the moment this is not supported.
      # For the record the logic looked in the results and did the following
      #   search for "Service Point"
      #   look ahead for <  and find sevice name within <>
      #   ignore if not "cms"
      #   look ahead for ":"
      #   look ahead for second ":"
      #   select characters until "/"
      #   result is alternate port number
      # try that as alternate port to access SOAP
   }

   # if not successful yet, work by retrieving the index.xml file
   #  This contains full information about what services are registered and the port number

   logit(0,"Trial SOAP connection failed, work with index.xml file");
   for (my $i=0; $i < 4; $i++) {
      if (($i == 0) and ($connect_attempthttps == 1)) {
         $connect_protocol = 'https' if $connect_protocolGiven == 0;
         $connect_port = '3661' if $connect_portGiven == 0;

      } elsif (($i == 1) and ($connect_attempthttps6 == 1)) {
         $DB::single=2 if $opt_debug == 1;
         $connect_protocol = 'https6' if $connect_protocolGiven == 0;
         $connect_port = '3661' if $connect_portGiven == 0;

      } elsif (($i == 2) and ($connect_attempthttp == 1)) {
         $connect_protocol = 'http' if $connect_protocolGiven == 0;
         $connect_port = '1920' if $connect_portGiven == 0;

      } elsif (($i == 3) and ($connect_attempthttp6 == 1)) {
         $DB::single=2 if $opt_debug == 1;
         $connect_protocol = 'http6' if $connect_protocolGiven == 0;
         $connect_port = '1920' if $connect_portGiven == 0;
      } else {
         next;
      }

      $test_connection = $connect_protocol . "://" . $connect_hostName . ":" . $connect_port . "/kdh/index/index.xml";
      logit(0,"Attempt retrievel of index.xml file using [$test_connection]");
      $oHub = SOAP::Lite->proxy($test_connection,timeout => $opt_soap_timeout);
      $oHub->outputxml('true');
      $oHub->on_fault( sub {});      # pass back all errors
      $connect_res = DoSoap('CT_Get_Object','Local_System_Command','raw');       # the 'raw' third parm means that DoSoap will not analyze results
      $run_status = 0;                                                           # reset error count
      next if $soap_rc != 0;                                                          # if severe error
      next if $soap_faultstr ne "";                                                   # or soap_faultstring, then exit
      next if substr($connect_res,0,1) ne '<';                                   # something bad happenned like timeout, ignore it

      eval {$result = $tpp->parse($connect_res)};                                # attempt to parse results
      if ($@ ne "") {
         logit(100,"error parsing index.xml results $@");
         next;
      }

      next if ref($result->{'kdh:servicepointlist'}->{'servicepoint'}) ne "ARRAY";  # array expected, else quit

      push(@results3,@{$result->{'kdh:servicepointlist'}->{'servicepoint'}});

      $connect_httpPortNo = "";                                                 # reset all potential results
      $connect_httpsPortNo = "";
      $connect_ip6PortNo = "";
      $connect_ips6PortNo = "";
      $connect_httpsFound = 0;
      $connect_httpFound = 0;
      $connect_https6Found = 0;
      $connect_http6Found = 0;

      foreach my $rr (@results3) {                                               # top level scan of services, looking for one that ends up "_cms"
         next if substr($rr->{'#text'},-4,4) ne '_cms';
         push(@results4,@{$rr->{'location'}->{'protocol'}});                     # capture protocol array
         foreach my $ss (@results4) {
            $in_protocol = $ss->{'#text'};
            if ($in_protocol eq "ip.ssl") {
               $DB::single=2 if $opt_debug == 1;
               $connect_httpsPortNo = $ss->{'endpoint'};
               $connect_httpsFound = 1;
            } elsif ($in_protocol eq "ip.tcp") {
               $connect_httpPortNo = $ss->{'endpoint'};
               $connect_httpFound = 1;
            } elsif ($in_protocol eq "ip6.ssl") {
               $DB::single=2 if $opt_debug == 1;
               next unless $opt_soap_lite_v6 == 1;
               $connect_ips6PortNo = $ss->{'endpoint'};
               $connect_https6Found = 1;
            } elsif ($in_protocol eq "ip6.tcpl") {
               $DB::single=2 if $opt_debug == 1;
               next unless $opt_soap_lite_v6 == 1;
               $connect_ip6PortNo = $ss->{'endpoint'};
               $connect_http6Found = 1;
            }
         }
      }

      # update the attempt variables based on the ports found
      $connect_attempthttps = 0;
      $connect_attempthttp  = 0;
      $connect_attempthttps6  = 0;
      $connect_attempthttp6  = 0;
      $connect_attempthttps = 1 if $connect_httpsPortNo ne "";
      $connect_attempthttp  = 1 if $connect_httpPortNo ne "";
      $connect_attempthttps6  = 1 if $connect_ips6PortNo ne "";
      $connect_attempthttp6  = 1 if $connect_ip6PortNo ne "";

      for (my $i=0; $i < 4; $i++) {
         if (($i == 0) and ($connect_attempthttps == 1)) {
            $DB::single=2 if $opt_debug == 1;
            $connect_protocol = 'https';
            $connect_port = $connect_httpsPortNo;
         } elsif (($i == 1) and ($connect_attempthttps6 == 1)) {
            $DB::single=2 if $opt_debug == 1;
            next unless $opt_soap_lite_v6 == 1;
            $connect_protocol = 'https6';
            $connect_port = $connect_ips6PortNo;
         } elsif (($i == 2) and ($connect_attempthttp == 1)) {
            $connect_protocol = 'http';
            $connect_port = $connect_httpPortNo;
         } elsif (($i == 3) and ($connect_attempthttp6 == 1)) {
            $DB::single=2 if $opt_debug == 1;
            next unless $opt_soap_lite_v6 == 1;
            $connect_protocol = 'http6';
            $connect_port = $connect_ip6PortNo;
         } else {next;}

         $test_connection = $connect_protocol . "://" . $connect_hostName . ":" . $connect_port . "///cms/soap";
         logit(0,"Trial SOAP connection based index.xml [$test_connection]");
         $oHub = SOAP::Lite->proxy($test_connection,timeout => $opt_soap_timeout);
         $oHub->outputxml('true');
         $oHub->on_fault( sub {});      # pass back all errors
         $connect_res = DoSoap('CT_Get_Object','Local_System_Command');
         $run_status = 0;
         if ($soap_rc == 0) {
            if ($soap_faultstr eq "") {
               logit(0,"SOAP connection success [$test_connection]");
               $connection = $test_connection;
               return 0;
            }
         }
      }  # end of analysis if single index.xml file
   }  # end of attempt to retrieve index files
logit(0,"unable to establish connection to SOAP server");
$run_status++;
}

# History log

# 1.00000  : New script based on ITM Health Survey 1.08000
# 1.01000  : Add -lst option and -gensql option
# 1.02000  : correct show SELECT sql problems
# 1.03000  : better parse_lst logic
# 1.05000  : Add creation of recycle command/shell files
# 1.06000  : generate only one recycle per agent
# 1.07000  : generate deletes only for TEMS with agents that might cause problems
#          : Add opt_exl to exclude some TEMSes
# 1.08000  : Identify cases where restart agents do not have online OS Agents
#          : Warn for cases where agent name does not have proper suffix
#          : Consolidate duplicated logic
# 1.09000  : Overlay output files
# 1.10000  : Handle multiple VT agents on single system
