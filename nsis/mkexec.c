/*                                                        */
/*                                                        */
/* Twelf Batch File Creator                               */
/*                                                        */
/* Arguments:                                             */
/* $1 = SMLNJ runtime                                     */
/* $2 = Twelf root directory                              */
/* $3 = Type of executable (e.g. twelf-server, twelf-sml) */
/*                                                        */

#include <stdio.h>

int main (int argc, char** argv)
{
	if (argc != 4)
		fprintf(stderr, "mkexec <SMLNJ runtime> <Twelf root> <type>\n %d", argc);
	else
		{
			char name [256];
			FILE *fp;

			sprintf (name, "%s\\bin\\%s.bat", argv[2], argv[3]);
			fp = fopen (name, "w+");
			printf ("Writing in %s:\n", name);
			printf ("@echo off\n");
			fprintf (fp, "@echo off\n");
			printf ("\"%s\" @SMLload=\"%s\\bin\\.heap\\%s\"\n", argv[1], argv[2], argv[3]);
			fprintf (fp, "\"%s\" @SMLload=\"%s\\bin\\.heap\\%s\"\n", argv[1], argv[2], argv[3]);
			fflush (fp);
			fclose (fp);
		}
	return 0;
}
