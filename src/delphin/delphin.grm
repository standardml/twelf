
(* s is a string consisting of an identifier, followed by one or more 
   whitespace characters other than newlines, followed by "::" *)
fun chop s = 
    let 
      fun stripws s' =
          let 
            val last = String.sub (s', size(s')-1)
          in
             case last 
               of #" "  => stripws (substring (s', 0, (size(s')-1))) 
                | #"\t" => stripws (substring (s', 0, (size(s')-1))) 
                | c     => s'
          end
    in stripws (substring (s, 0, size(s)-2))
    end 
  

structure D = DextSyn'
structure L = Lexer

%%

%name Delphin
%pos int
%header (functor DelphinLrValsFun (structure Token : TOKEN
                                   structure DextSyn' : DEXTSYN))
%eop EOF
%noshift EOF
%verbose


%term    ID of string 
       | COLON 
       | DOT 
       | EQUAL 
       | DBLCOLON 
       | BLOCKDEC
       | BLOCK of string
       | CREATE
       | VAL 
       | FUN
       | CASE
       | OF
       | BAR
       | LET 
       | IN 
       | END 
       | NEW
       | CHOOSE 
       | SOME of string 
       | ALL 
       | EXISTS
       | ALLOMITTED
       | EXISTSOMITTED
       | TYPE  
       | RTARROW  
       | LTARROW 
       | RTPAREN  
       | LTPAREN
       | RTBRACKET  
       | LTBRACKET  
       | RTBRACE 
       | LTBRACE  
       | AND 
       | DBLARROW  
       | COMMA  
       | PAR
       | EOF 
       | LTANGLE 
       | RTANGLE 
       | TRUE 
       | UNIT 
       | LLAM 
       | RLAM 
       | AT
       | TIMES   
       | PLUS   
       | UNDERSCORE
       | WORLD
       | FORMID of string
       | PREC0
       | PREC1 
       | PREC2
       | PREC3

%nonterm    start of D.Ast
          | decs of D.Decs 
          | formdecl of D.FormDecl
	  | fundecl of D.FunDecl
          | valdecl of D.ValDecl
	  | createdecl of D.CreateDecl
          | term of D.Term 
          | cases of D.Cases 
          | dec of D.Dec
          | form of D.Form
          | head of D.Head
          | mdec of D.MDec 
          | pat of D.Pat  
          | prog of D.Prog
	  | world of D.World
          | id of string
          | lfdecs of D.Dec list




%left PREC0
%left PREC1
%left PREC2
%left PREC3
%left COLON LTARROW
%left AND
%left TIMES
%left PLUS

%right DOT
%right DBLCOLON
%right ID FORMID TRUE ALL EXISTS ALLOMITTED EXISTSOMITTED VAL FUN CASE OF BAR LET CREATE IN END NEW CHOOSE
%right RTARROW DBLARROW 

%nonassoc PAR UNDERSCORE AT
%nonassoc LTPAREN RTPAREN LTBRACE RTBRACE LTBRACKET RTBRACKET LLAM RLAM
%nonassoc LTANGLE RTANGLE

%start start

%%

start     : decs                           %prec PREC0        	(D.Ast decs)
          
decs      :                  		   %prec PREC1          (D.Empty)
          | fundecl decs     		   %prec PREC1    	(D.FunDecl (fundecl, decs))  
          | formdecl decs    		   %prec PREC1    	(D.FormDecl (formdecl, decs))  
          | valdecl decs                   %prec PREC1    	(D.ValDecl (valdecl, decs))    
	  | NEW LTPAREN dec RTPAREN  decs  %prec PREC1          (D.NewDecl (dec, decs))
	  | dec decs 			   %prec PREC1		(D.TwelfDecl (dec, decs))
	  | createdecl decs 		   %prec PREC1          (D.CreateDecl (createdecl, decs))

createdecl : CREATE term createdecl 	   %prec PREC2          (D.Create (term, createdecl))
           | valdecl END                   %prec PREC2          (D.Decs (D.ValDecl(valdecl, D.Empty)))

formdecl  : FORMID form			   %prec PREC2          (D.Form (chop (FORMID), form))

fundecl   : FUN head EQUAL prog 	   %prec PREC2          (D.Fun (head, prog))
          | BAR head EQUAL prog 	   %prec PREC2          (D.Bar (head, prog)) 
          | AND head EQUAL prog 	   %prec PREC2          (D.FunAnd (head, prog)) 

valdecl   : VAL pat DBLCOLON form EQUAL prog %prec PREC2        (D.Val (pat, prog, SOME form))
	  | VAL pat EQUAL prog 		     %prec PREC2        (D.Val (pat, prog, NONE))


term      : TYPE   			   %prec PREC3          (D.Type)
          | ID     			   %prec PREC3          (D.Id (chop ID))
          | TRUE   			   %prec PREC3          (D.Id "true")
          | AND    			   %prec PREC3          (D.Id "and")
          | ALL                            %prec PREC3          (D.Id "all")
          | ALLOMITTED                     %prec PREC3          (D.Id "all^")
          | EXISTS                         %prec PREC3          (D.Id "exists")
          | EXISTSOMITTED                  %prec PREC3          (D.Id "exists^")
          | VAL                            %prec PREC3          (D.Id "val") 
          | FUN                            %prec PREC3          (D.Id "fun")
          | CASE                           %prec PREC3          (D.Id "case")
          | OF                             %prec PREC3          (D.Id "of")
  	  | PAR	                           %prec PREC3		(D.Id "||")
          | BAR                            %prec PREC3          (D.Id "|")
          | LET                            %prec PREC3          (D.Id "let") 
          | TIMES  		           %prec PREC3		(D.Id "*")
          | PLUS                           %prec PREC3          (D.Id "+")
          | IN                             %prec PREC3          (D.Id "in")
          | END                            %prec PREC3     	(D.Id "end") 
          | NEW                            %prec PREC3       	(D.Id "new")
          | CHOOSE                         %prec PREC3       	(D.Id "choose")
          | term RTARROW term              %prec PREC3	        (D.Rtarrow (term1, term2))
          | term LTARROW term              %prec PREC3	        (D.Ltarrow (term1, term2))
          | LTBRACE dec RTBRACE term       %prec PREC3 	        (D.Pi (dec, term)) 
          | LTBRACKET dec RTBRACKET term   %prec PREC3 	        (D.Fn (dec, term))
          | LTPAREN term RTPAREN           %prec PREC3	        (D.Paren term)
          | ID term                        %prec PREC3 	        (D.App (D.Id ID, term))
          | TRUE term                      %prec PREC3          (D.App (D.Id "true", term))
          | AND term                       %prec PREC3          (D.App (D.Id "and", term))
          | ALL term                       %prec PREC3          (D.App (D.Id "all", term))
          | ALLOMITTED term                %prec PREC3          (D.App (D.Id "all^", term)) 
          | EXISTS term                    %prec PREC3          (D.App (D.Id "exists", term))
          | EXISTSOMITTED term             %prec PREC3          (D.App (D.Id "exists^", term))
          | VAL term                       %prec PREC3          (D.App (D.Id "val", term))
          | FUN term                       %prec PREC3          (D.App (D.Id "fun", term))
          | CASE term                      %prec PREC3          (D.App (D.Id "case", term))
          | OF term                        %prec PREC3          (D.App (D.Id "of", term))
          | BAR term                       %prec PREC3          (D.App (D.Id "|", term))
          | PAR term                       %prec PREC3          (D.App (D.Id "||", term))
          | LET term                       %prec PREC3          (D.App (D.Id "let", term))
          | IN term                        %prec PREC3          (D.App (D.Id "in", term))
          | END term                       %prec PREC3          (D.App (D.Id "end", term)) 
          | NEW term                       %prec PREC3          (D.App (D.Id "new", term))  
          | CHOOSE term                    %prec PREC3          (D.App (D.Id "choose", term))  
          | UNDERSCORE term                %prec PREC3       	(D.Omit)
          | LTPAREN term RTPAREN term      %prec PREC3      	(D.App (D.Paren term1, term2))
          | term COLON term                %prec PREC3        	(D.Of (term1, term2))
          | UNDERSCORE                     %prec PREC3        	(D.Omit)  
          | term DOT ID 	           %prec PREC3		(D.Dot (term1, ID))

world     : LTPAREN world RTPAREN %prec PREC1                   (world)
          | ID                    %prec PREC1                   (D.WorldIdent ID)
	  | world world           %prec PREC1                   (D.Concat (world1, world2))
	  | world PLUS world      %prec PREC1                   (D.Plus (world, world))
	  | world TIMES           %prec PREC1                   (D.Times world)

dec       : ID COLON term         %prec PREC1                   (D.Dec (ID, term))
          | ID                    %prec PREC1           	(D.Dec (ID, D.Omit))

form      : WORLD world form                       %prec PREC0  (D.World (world, form))
	  | ALL LTBRACE dec RTBRACE form           %prec PREC0  (D.Forall (dec, form))
	  | ALLOMITTED LTBRACE dec RTBRACE form    %prec PREC0  (D.ForallOmitted (dec, form))
          | EXISTS LTBRACE dec RTBRACE form   	   %prec PREC0  (D.Exists (dec, form))
          | EXISTSOMITTED LTBRACE dec RTBRACE form %prec PREC0  (D.ExistsOmitted (dec, form))
          | form AND form                          %prec PREC0  (D.And (form1, form2))
          | LTPAREN form RTPAREN              	   %prec PREC0  (form)
          | TRUE                                   %prec PREC0  (D.True)

prog      : ID                                                  (D.Const (ID))
          | prog ID              	                        (D.AppTerm (prog, D.Id ID)) 
          | prog UNDERSCORE                   	                (D.AppTerm (prog, D.Id "_"))
          | prog LTPAREN term RTPAREN         	                (D.AppTerm (prog, term))
          | LTPAREN prog RTPAREN              	                (prog)
          | UNIT                              	                (D.Unit)
	  | CASE prog OF cases                                  (D.Unit)
	  | prog PAR prog			                (D.Par (prog1, prog2))
          | LTPAREN prog COMMA prog RTPAREN   	                (D.Pair (prog1, prog2))   
          | prog AT prog                      	                (D.AppProg (prog1, prog2))
          | LTANGLE term COMMA prog RTANGLE   	                (D.Inx (term, prog))  
          | LLAM dec RLAM prog               	                (D.Lam (dec, prog))   
          | LET decs IN prog END              	                (D.Let (decs, prog)) 
	  | NEW lfdecs IN prog END	                        (D.New (lfdecs, prog))
	  | CHOOSE LTPAREN dec RTPAREN  IN prog END	        (D.Choose (dec, prog))

lfdecs    :                       		         	(nil)
	  | LTPAREN dec RTPAREN lfdecs		         	(dec :: lfdecs)

cases     : pat DBLARROW prog  %prec PREC0                      (D.First (pat, prog))
          | cases BAR pat DBLARROW prog %prec PREC1             (D.Alt  (cases, pat, prog)) 

head      : ID                       		                (D.Head (ID))
          | head ID                           	                (D.AppLF (head, D.Id ID))     
          | head UNDERSCORE                   	                (D.AppLF (head, D.Omit))
          | head LTPAREN term RTPAREN         	                (D.AppLF (head, term))
          | head AT pat                       	                (D.AppMeta (head, pat))

mdec      : ID                                                  (D.MDec (ID, NONE))
          | FORMID form                      	                (D.MDec (chop (FORMID), SOME (form)))
         
pat       : mdec                                                (D.PatVar (mdec))
          | LTPAREN pat COMMA pat RTPAREN     	                (D.PatPair (pat1, pat2))
          | LTANGLE term COMMA pat RTANGLE    	                (D.PatInx (term, pat))
          | UNIT                              	                (D.PatUnit)
          | UNDERSCORE                        	                (D.PatUnderscore)