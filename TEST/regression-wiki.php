<?php

$link =
  mysql_connect('localhost', 'twelfwiki', $argv[1])
  or die ('Database connection failed');
mysql_select_db('twelfwiki', $link)
  or die ('Database selection failed');

$literatepages = mysql_query(			     
"select cl_sortkey from categorylinks where cl_to='Literate_Twelf_code'");

$file = fopen("regression-wiki.txt", "w");

while($row = mysql_fetch_array($literatepages)) {
  $page = $row[0];
  $codepage = strtr($page," :/","___");

  $ignore = false;
  $unsafe = false;

  if($page == "Double-negation translation")                $unsafe = true;
  if($page == "POPL Tutorial/Big step, small step")         $ignore = true;
  if($page == "POPL Tutorial/Exceptions-problem")           $ignore = true;
  if($page == "POPL Tutorial/MinML Preservation Theorem")   $ignore = true;
  if($page == "POPL Tutorial/MinML encoding")               $ignore = true;
  if($page == "POPL Tutorial/Sequent vs Natural Deduction") $ignore = true;
  if($page == "POPL Tutorial/Session 2 Script")             $ignore = true;
  if($page == "POPL Tutorial/Session 4 Live")               $ignore = true;
  if($page == "POPL Tutorial/Typed bracket abstraction")    $ignore = true;
  if($page == "Polarized PCF")                              $unsafe = true;
  if($page == "User:Hdeyoung/monweakfoc")                   $unsafe = true;
  if($page == "") $ignore = true;
  if($page == "") $ignore = true;
  if(substr($page,0,25) == "Computation and Deduction")     $ignore = true;

  $twelfcode = file_get_contents('http://twelf.plparty.org/'
				 . 'w/index.php?title='
				 . urlencode($page)
				 . '&action=raw&ctype=text%2Fcss');


  if(!$ignore) { 
    if($unsafe) $cmd = "testUnsafe";
    else $cmd = "test";

    fwrite($file, $cmd . " ../TEST/wiki-examples/" . $codepage . ".cfg\n");
    
    $elffile = fopen ("wiki-examples/" . $codepage . ".elf", "w");
    fwrite($elffile, $twelfcode);
    fclose ($elffile);  
    
    $cfgfile = fopen ("wiki-examples/" . $codepage . ".cfg", "w");
    fwrite($cfgfile, $codepage . ".elf\n");
    fclose ($cfgfile);  
  }
}

fclose($file);