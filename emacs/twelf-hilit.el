;;; twelf-hilite.el.  Highlighting for twelf-mode using hilit19.
;;;
;;; Author: Frank Pfenning
;;; Fri Mar  1 15:37:24 1996 (created)
;;;
;;; Documentation still has to be written.
;;; There is only one new key binding in Twelf mode
;;;
;;; C-c C-g      remove temporary highlight of range and focus.
;;;
;;; This is long out of date
;;; Thu Apr  4 22:03:10 2002

(require 'hilit19)
(require 'twelf)

;; modify the syntax table so _ and ' are word constituents
;; otherwise the regexp's for identifiers become very complicated
(set-word ?\_)
(set-word ?\')
;; for LLF
(set-twelf-syntax ?, ".   ")
(set-twelf-syntax ?^ ".   ")

(cond ((and (x-display-color-p) (eq hilit-background-mode 'light))
       (hilit-translate twelf-comment	'firebrick-italic)
       (hilit-translate twelf-pragma	'mediumpurple)
       (hilit-translate twelf-keyword	'default)
       (hilit-translate twelf-decl        'firebrick)
       (hilit-translate twelf-parm        'green4)
       (hilit-translate twelf-fvar        'blue1)
       (hilit-translate twelf-evar        'blue4))
      ((and (x-display-color-p) (eq hilit-background-mode 'dark))
       (hilit-translate twelf-comment	'moccasin-italic)
       (hilit-translate twelf-pragma	'plum)
       (hilit-translate twelf-keyword	'default)
       (hilit-translate twelf-decl        'orange)
       (hilit-translate twelf-parm        'orange)
       (hilit-translate twelf-fvar        'springgreen)
       (hilit-translate twelf-evar        'aquamarine))
      (t
       (hilit-translate twelf-comment	'italic)
       (hilit-translate twelf-pragma	'bold)
       (hilit-translate twelf-keyword	'nil)
       (hilit-translate twelf-decl        'nil)
       (hilit-translate twelf-parm        'nil)
       (hilit-translate twelf-fvar        'nil)
       (hilit-translate twelf-evar        'nil)))

(hilit-set-mode-patterns
 'twelf-mode
 '(
   ;; %keyword declarations
   ("\\(%infix\\|%prefix\\|%prefix\\|%postfix\\|%name\\|%solve\\|%query\\|%mode\\|%terminates\\|%theorem\\|%prove\\|%assert\\|%establish\\).*$"
    1 twelf-pragma)
   ;; single-line comments
   ("%\\W.*$" nil twelf-comment)
   ;; delimited comments, perhaps should use different font
   ;; nests correctly??
   ;;("%{" "}%" comment)
   (hilit-twelf-find-delimited-comment nil twelf-comment)
   ;; keywords, omit punctuations for now.
   ("\\(\\<<-\\>\\|\\<->\\>\\|\\<type\\>\\|\\<=\\>\\|\\<_\\>\\)"
   ;; being somewhat sloppy, I am adding LLF constants here
   ;;"\\(\\<<-\\>\\|\\<->\\>\\|\\<type\\>\\|\\<=\\>\\|\\<_\\>\\)"
   ;;   ("\\(\\<<-\\>\\|\\<->\\>\\|\\<o-\\>\\|\\<-o\\>\\|\\<<T>\\>\\|\\<&\\>\\|\\^\\|()\\|\\<type\\>\\|\\<sigma\\>\\)"
    ;; for LLF, with punctuation marks
    ;;"\\([][:.(){},]\\|\\<<-\\>\\|\\<->\\>\\|\\<o-\\>\\|\\<-o\\>\\|\\<<T>\\>\\|\\<&\\>\\|\\^\\|()\\|\\<type\\>\\|\\<sigma\\>\\)"
    ;; for Elf, no punction marks
    ;;"\\(\\<<-\\>\\|\\<->\\>\\|\\<type\\>\\|\\<sigma\\>\\)" 
    ;; for Twelf, including punctuation marks
    ;;"\\([][:.(){}]\\|\\<<-\\>\\|\\<->\\>\\|\\<type\\>\\|\\<sigma\\>\\)"
   nil twelf-keyword)
   ;; declared constants
   (hilit-twelf-find-decl nil twelf-decl)
   ;; parameters
   (hilit-twelf-find-parm nil twelf-parm)
   ;; quantified existentials
   (hilit-twelf-find-evar nil twelf-evar)
   ;; lower-case identifiers (almost = constants)
   ;;("\\<\\([a-z!&$^+/<=>?@~|#*`;,]\\|\\-\\|\\\\\\)\\w*\\>"
   ;; nil black)
   ;; upper-case identifiers (almost = variables)
   ("\\<[A-Z_]\\w*\\>" nil twelf-fvar)
   ;; numbers and quoted identifiers omitted for now
   ;; can we parse for the declarations of constants??
   ))

(defun hilit-twelf-find-delimited-comment (qchar)
  "Find a delimited Twelf comment and return (START . END), nil if none."
  (let ((comment-level nil)
	(comment-start nil))
    (if (search-forward "%{" nil t)
	(progn
	  (setq comment-start (- (point) 2))
	  (setq comment-level 1)
	  (while (and (> comment-level 0)
		      (re-search-forward "\\(%{\\)\\|\\(}%\\)"
					 nil 'limit))
	    (cond
	     ((match-beginning 1) (setq comment-level (1+ comment-level)))
	     ((match-beginning 2) (setq comment-level (1- comment-level)))))
	  (cons comment-start (point)))
      nil)))

(defun hilit-twelf-find-decl (qchar)
  "Find an Twelf constant declaration and return (START . END), nil if none.
Always returns nil query minor mode."
  (let (start
	end
	(id (twelf-next-decl (buffer-file-name) (new-temp-buffer))))
    (if (null id)
	nil
      (skip-chars-backward *whitespace*)
      (setq end (point))
      (beginning-of-line 1)
      (setq start (point))
      (twelf-end-of-par)
      (cons start end))))

(defun hilit-twelf-find-binder (var-pattern)
  "Find Twelf binder whose bound variable matches var-pattern.
Returns (START . END) if found, NIL if there is none.
Binders have the form [x],[x:A],{y},{y:A}.
As a side-effect, it highlights all occurrences of the bound
variable using the (dynamically bound) variables FACE and PRIO.
They are bound in function hilit-highlight-region in hilit19.el."
  (let (start
	end
	limit
	scope-start
	scope-end
	word
	(found nil))
    (while (not found)
      (skip-chars-forward "^[{%")
      (while (looking-at *twelf-comment-start*)
	(cond ((looking-at "%{")
	       (condition-case nil (forward-sexp 1)
		 (error (goto-char (point-max))))
	       (or (eobp) (forward-char 1)))
	      (t
	       (end-of-line 1)))
	(skip-chars-forward "^[{%"))
      (if (eobp)
	  (setq found 'eob)
	(forward-char 1)
	(skip-chars-forward *whitespace*)
	(if (looking-at var-pattern)
	    ;;"\\<\\w+\\>"
	    ;;"\\<[-a-z!&$^+/\\<=>?@~|#*`;,]\\w*\\>"
	    (setq found t))))
    (if (eq found 'eob)
	nil
      (setq start (match-beginning 0))
      (setq end (match-end 0))
      (setq word (buffer-substring start end))
      ;; find scope of quantifier
      (twelf-end-of-par)
      (setq limit (point))
      (goto-char end)
      (condition-case nil (up-list 1)	; end of quantifier
	(error (goto-char limit)))
      (setq scope-start (min (point) limit))
      (condition-case nil (up-list 1)	; end of scope
	(error (goto-char limit)))
      (setq scope-end (min (point) limit))
      (goto-char scope-start)
      (while
	  (search-forward-regexp (concat "\\<" (regexp-quote word) "\\>")
				 scope-end 'limit)
	;; !!! NOTE: DYNAMIC SCOPE EXPLOITED HERE !!!
	(hilit-region-set-face (match-beginning 0) (match-end 0)
			       face prio))
      (goto-char end)
      (cons start end))))

(defun hilit-twelf-find-parm (qchar)
  "Find bound Twelf parameters and return (START . END), NIL if none.
Also highlights all occurrences of the parameter.
For these purposes, a parameter is a bound, lower-case identifier."
  (hilit-twelf-find-binder "\\<[-a-z!&$^+/\\<=>?@~|#*`;,]\\w*\\>"))

(defun hilit-twelf-find-evar (qchar)
  "Find bound Twelf existential variable return (START . END), NIL if none.
Also highlights all occurrences of the existential variable.
For these purposes, an existential variable is a bound, upper-case identifier."
  (hilit-twelf-find-binder "\\<[A-Z_]\\w*\\>"))

;;; Redefine some functions for nicer display

(defvar twelf-range-overlay nil
  "Overlay for the current range in Twelf.")

(defun twelf-range-overlay ()
  (or twelf-range-overlay 
      (progn
	(setq twelf-range-overlay (make-overlay (point-min) (point-min)))
	(overlay-put twelf-range-overlay 'face 'highlight)
	twelf-range-overlay)))

(defun hilit-twelf-highlight-range (start end)
  "Highlight range of error or other server interaction."
  (move-overlay (twelf-range-overlay) start end (current-buffer)))

(defun hilit-twelf-unhighlight-range ()
  "Unhilight range of error or other server interaction."
  (interactive)
  (move-overlay (twelf-range-overlay) 0 0))

(setq twelf-highlight-range-function 'hilit-twelf-highlight-range)

(make-face 'twelf-focus-face)
(cond ((and (x-display-color-p) (eq hilit-background-mode 'light))
       (set-face-background 'twelf-focus-face "lightyellow"))
      ((and (x-display-color-p) (eq hilit-background-mode 'dark))
       (set-face-background 'twelf-focus-face "darkslategray"))) 

(defvar twelf-focus-overlay nil
  "Overlay for current focus in Twelf.")

(defun twelf-focus-overlay ()
  (or twelf-focus-overlay
      (progn
	(setq twelf-focus-overlay (make-overlay (point-min) (point-min)))
	(overlay-put twelf-focus-overlay 'face 'twelf-focus-face)
	twelf-focus-overlay)))

(defun hilit-twelf-focus (start end)
  "Focus on region by re-highlighting."
  (cond ((and (null start) (null end) (eq major-mode 'twelf-mode))
	 ;; Re-highlight whole buffer in Twelf mode if no particular focus.
	 (hilit-rehighlight-buffer hilit-quietly))
	((and start end)
	 ;; Re-highlight focus region quietly
	 (hilit-rehighlight-region start end t)
	 (move-overlay (twelf-focus-overlay) start end (current-buffer)))
	(t 
	 ;; Do nothing otherwise
	 nil)))

(defun hilit-twelf-unfocus ()
  (interactive)
  (move-overlay (twelf-focus-overlay) 0 0))

(setq twelf-focus-function 'hilit-twelf-focus)

;;; New key assignments

(defun hilit-twelf-relax ()
  "Unhighlight range and blur focus."
  (interactive)
  (hilit-twelf-unhighlight-range)
  (hilit-twelf-unfocus))

(define-key twelf-mode-map "\C-c\C-g" 'hilit-twelf-relax)

(provide 'twelf-hilit)
