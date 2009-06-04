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

  print ($codepage) . "\n";

  $twelfcode = file_get_contents('http://twelf.plparty.org/'
				 . 'w/index.php?title='
				 . urlencode($page)
				 . '&action=raw&ctype=text%2Fcss');


  fwrite($file, "test ../TEST/wiki-examples/" . $codepage . ".cfg\n");

  $elffile = fopen ("wiki-examples/" . $codepage . ".elf", "w");
  fwrite($elffile, $twelfcode);
  fclose ($elffile);  
 
  $cfgfile = fopen ("wiki-examples/" . $codepage . ".cfg", "w");
  fwrite($cfgfile, $codepage . ".elf\n");
  fclose ($cfgfile);  
}

fclose($file);