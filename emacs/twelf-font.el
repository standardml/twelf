;;; twelf-font.el.  Highlighting for Twelf mode using font-lock in XEmacs
;;;
;;; Author: Frank Pfenning
;;; Fri Mar  1 15:37:24 1996 (created hilit mode)
;;;
;;; WARNING: do not compile this file if you want to load it into
;;; FSF Emacs and XEmacs, since the inlined functions (defsubst ...)
;;; in font-lock will not work across different Emacs versions.
;;;
;;; Documentation still has to be written.
;;; There are two new key binding in Twelf mode
;;;
;;; C-c C-l   fontifies current Twelf declaration
;;; C-c l     fontifies current buffer
;;;
;;; New user functions (current DISABLED!!!)
;;;
;;; M-x twelf-font-install-immediate
;;; M-x twelf-font-uninstall-immediate
;;;   when "immediate" is installed it tries to fontify as you type
;;;   Currently this is a rather gross, unstable hack, so beware!
;;;
;;; M-x twelf-font-unfontify
;;;   unfontifies the current buffer
;;;
;;; For your .emacs file:
;;; (add-hook 'twelf-mode-hook 'twelf-font-fontify-buffer)

(require 'font-lock)
(require 'twelf)

;; modify the syntax table so _ and ' are word constituents
;; otherwise the regexp's for identifiers become very complicated
(set-word ?\_)
(set-word ?\')

;; for LLF
;(set-twelf-syntax ?, ".   ")
;(set-twelf-syntax ?^ ".   ")

;; for FSF Emacs 19
(if (not (fboundp 'font-lock-any-faces-p))
    (defun font-lock-any-faces-p (start end)
      (text-property-not-all start end 'face nil)))

;; for FSF Emacs 19
(if (not (fboundp 'font-lock-set-face))
    (defun font-lock-set-face (start end face)
      (put-text-property start end 'face face)))

;; for FSF Emacs 19
(if (and (boundp 'font-lock-face-attributes)
	 (null font-lock-face-attributes))
    (font-lock-make-faces))

;; Setting faces here...
;; use devices to improve portability?
;; make it dependent on light background vs dark background
;; tie in X resources?

(defun twelf-font-create-face (face from-face color)
  "Creates a Twelf font from FROM-FACE with COLOR."
  (make-face face)
  ;(reset-face face)			; seems to be necessary, but why?
  (copy-face from-face face)
  (if color (set-face-foreground face color)))

(defvar twelf-font-dark-background nil
  "*T if the background of Emacs is to be considered dark.")

;; currently we not using bold or italics---some font families
;; work poorly with that kind of face.
(cond (twelf-font-dark-background
       (twelf-font-create-face 'twelf-font-keyword-face 'font-lock-comment-face nil)
       (twelf-font-create-face 'twelf-font-const-face 'font-lock-comment-face nil)
       (twelf-font-create-face 'twelf-font-comment-face 'font-lock-comment-face
			     nil)
       (twelf-font-create-face 'twelf-font-percent-key-face 'font-lock-comment-face "Plum")
       (twelf-font-create-face 'twelf-font-decl-face 'font-lock-comment-face "Orange")
       (twelf-font-create-face 'twelf-font-parm-face 'font-lock-comment-face "Orange")
       (twelf-font-create-face 'twelf-font-fvar-face 'font-lock-comment-face "SpringGreen")
       (twelf-font-create-face 'twelf-font-evar-face 'font-lock-comment-face "Aquamarine"))
      (t 
       (twelf-font-create-face 'twelf-font-keyword-face 'font-lock-comment-face nil)
       (twelf-font-create-face 'twelf-font-const-face 'font-lock-comment-face nil)
       (twelf-font-create-face 'twelf-font-comment-face 'font-lock-comment-face
			     nil)
       (twelf-font-create-face 'twelf-font-percent-key-face 'font-lock-comment-face "MediumPurple")
       (twelf-font-create-face 'twelf-font-decl-face 'font-lock-comment-face "FireBrick")
       (twelf-font-create-face 'twelf-font-parm-face 'font-lock-comment-face "Green4")
       (twelf-font-create-face 'twelf-font-fvar-face 'font-lock-comment-face "Blue1")
       (twelf-font-create-face 'twelf-font-evar-face 'font-lock-comment-face "Blue4")))

;; Note that the order matters!

(defvar twelf-font-patterns
 '(
   ;; delimited comments, perhaps should use different font
   ;;("%{" "}%" comment)
   (twelf-font-find-delimited-comment . twelf-font-comment-face)
   ;; empty-line comments
   ("%$" 0 twelf-font-comment-face)
   ;; single-line comments
   ("%[% \t\f].*$" 0 twelf-font-comment-face)
   ;; %keyword declarations
   ("\\(%infix\\|%prefix\\|%postfix\\|%name\\|%subord\\|%freeze\\|%thaw\\|%abbrev\\|%clause\\|%define\\|%solve\\|%querytabled\\|%query\\|%tabled\\|%deterministic\\|%mode\\|%unique\\|%block\\|%worlds\\|%covers\\|%total\\|%terminates\\|%reduces\\|%theorem\\|%prove\\|%assert\\|%establish\\|%sig\\|%struct\\|%trustme\\|%where\\|%include\\|%open\\|%use\\).*$"
    1 twelf-font-percent-key-face nil)
   ;; keywords, omit punctuations for now.
   ("\\(\\<<-\\>\\|\\<->\\>\\|\\<type\\>\\|\\<=\\>\\|\\<_\\>\\)"
    ;; for LLF, no punctuation marks
;;"\\(\\<<-\\>\\|\\<->\\>\\|\\<o-\\>\\|\\<-o\\>\\|\\<<T>\\>\\|\\<&\\>\\|\\^\\|()\\|\\<type\\>\\|\\<sigma\\>\\)"
    ;; for LLF, with punctuation marks
    ;;"\\([][:.(){},]\\|\\<<-\\>\\|\\<->\\>\\|\\<o-\\>\\|\\<-o\\>\\|\\<<T>\\>\\|\\<&\\>\\|\\^\\|()\\|\\<type\\>\\|\\<sigma\\>\\)"
    ;; for Elf, no punction marks
    ;;"\\(\\<<-\\>\\|\\<->\\>\\|\\<type\\>\\|\\<sigma\\>\\)" 
    ;; for Elf, including punctuation marks
    ;;"\\([][:.(){}]\\|\\<<-\\>\\|\\<->\\>\\|\\<type\\>\\|\\<sigma\\>\\)"
   . twelf-font-keyword-face)
   ;; declared constants
   (twelf-font-find-decl . twelf-font-decl-face)
   ;; parameters
   (twelf-font-find-parm . twelf-font-parm-face)
   ;; quantified existentials
   (twelf-font-find-evar . twelf-font-evar-face)
   ;; lower-case identifiers (almost = constants)
   ;;("\\<\\([a-z!&$^+/<=>?@~|#*`;,]\\|\\-\\|\\\\\\)\\w*\\>"
   ;; nil black)
   ;; qualified identifiers
   ("\\<\\w+\\(\\.\\w+\\)+\\>" . twelf-font-const-face)
   ;; upper-case identifiers (almost = variables)
   ("\\<[A-Z_]\\w*\\>" . twelf-font-fvar-face)
   ;; numbers and quoted identifiers omitted for now
   )
 "Highlighting patterns for Twelf mode.
This generally follows the syntax of the FONT-LOCK-KEYWORDS variable,
but allows an arbitrary function to be called instead of just
regular expressions."
 )

;;; Section below on "installation" currently not recommended.
;;; Begin experimental section
;(defvar font-lock-fontify-region-original nil
;  "Contains the original definition of FONT-LOCK-FONTIFY-REGION.
;Used to uninstall immediate highlighting in Twelf mode.")

;(defun toggle-twelf-font-immediate ()
;  "Toggle immediate highlighting option in Twelf mode.
;This is tied to font-lock mode."
;  (interactive)
;  (if font-lock-mode
;      (twelf-font-uninstall-immediate)
;    (twelf-font-install-immediate)))

;(defun twelf-font-install-immediate ()
;  "Turn on immediate highlighting.
;Caution: this redefines FONT-LOCK-FONTIFY-REGION."
;  (interactive)
;  (if (not font-lock-fontify-region-original)
;      (setq font-lock-fontify-region-original
;	    (symbol-function 'font-lock-fontify-region)))
;  (fset 'font-lock-fontify-region 'twelf-font-hacked-fontify-region)
;  (font-lock-mode t))

;(defun twelf-font-uninstall-immediate ()
;  "Turn off immediate highlighting.
;This attempts to re-install the old definition of FONT-LOCK-FONTIFY-REGION."
;  (interactive)
;  (if font-lock-fontify-region-original
;      (fset 'font-lock-fontify-region font-lock-fontify-region-original))
;  (font-lock-mode nil))

;(defun twelf-font-hacked-fontify-region (start end)
;  (if (eq major-mode 'twelf-mode)
;      (twelf-font-fontify-region start end)
;    (funcall font-lock-fontify-region-original start end)))
;;; End experimental section

(defun twelf-font-fontify-decl  ()
  "Fontifies the current Twelf declaration."
  (interactive)
  (let* ((inhibit-read-only t)		; for FSF Emacs
	 (region (twelf-current-decl))
	 (start (nth 0 region))
	 (end (nth 1 region)))
    (save-excursion
      (font-lock-unfontify-region start end)
      (twelf-font-fontify-region start end))))

(defun twelf-font-fontify-buffer ()
  "Fontitifies the current buffer as Twelf code."
  (interactive)
  (let ((inhibit-read-only t))		; for FSF Emacs
    (if (not twelf-config-mode)
	(save-excursion
	  (font-lock-unfontify-region (point-min) (point-max)) ; t optional in XEmacs
	  (twelf-font-fontify-region (point-min) (point-max))))))

(defun twelf-font-unfontify ()
  "Removes fontification from current buffer."
  (interactive)
  (font-lock-unfontify-region (point-min) (point-max)))	; t optional in XEmacs

(defvar font-lock-message-threshold 6000) ; in case we are running FSF Emacs

(defun twelf-font-fontify-region (start end)
  "Go through TWELF-FONT-PATTERNS, fontifying according to given functions"
  (save-restriction
    (narrow-to-region start end)
    (if (and font-lock-verbose
	     (>= (- end start) font-lock-message-threshold))
	(message "Fontifying %s... (semantically...)" (buffer-name)))
    (let ((patterns twelf-font-patterns)
	  (case-fold-search nil)	; in Twelf, never case-fold
	  (modified (buffer-modified-p)) ; for FSF Emacs 19
	  pattern
	  fun-or-regexp
	  instructions
	  face
	  match-index
	  allow-overlap-p
	  region)
      (while patterns
	(setq pattern (car patterns))
	(setq patterns (cdr patterns))
	(goto-char start)
	(cond ((stringp pattern)
	       (setq match-index 0)
	       (setq face 'font-lock-keyword-face)
	       (setq allow-overlap-p nil))
	      ((listp pattern)
	       (setq fun-or-regexp (car pattern))
	       (setq instructions (cdr pattern))
	       (cond ((integerp instructions)
		      (setq match-index instructions)
		      (setq face 'font-lock-keyword-face)
		      (setq allow-overlap-p nil))
		     ((symbolp instructions)
		      (setq match-index 0)
		      (setq face instructions)
		      (setq allow-overlap-p nil))
		     ((listp instructions)
		      (setq match-index (nth 0 instructions))
		      (setq face (nth 1 instructions))
		      (setq allow-overlap-p (nth 2 instructions)))
		     (t (error "Illegal font-lock-keyword instructions"))))
	      (t (error "Illegal font-lock-keyword instructions")))
	(cond ((symbolp fun-or-regexp)	; a function to call
	       (while 
		   (setq region (funcall fun-or-regexp end))
		 ;; END is limit of forward search, start at point
		 ;; and move point
		 ;; check whether overlap is permissible!
		 (twelf-font-highlight (car region) (cdr region)
				     face allow-overlap-p)))
	      ((stringp fun-or-regexp)	; a pattern to find
	       (while
		   (re-search-forward fun-or-regexp end t)
		 (goto-char (match-end match-index)) ; back-to-back font hack
		 (twelf-font-highlight (match-beginning match-index)
				     (match-end match-index)
				     face
				     allow-overlap-p)))
	      (t (error "Illegal font-lock-keyword instructions"))))
      ;; For FSF Emacs 19: mark buffer not modified, if it wasn't before
      ;; fontification.
      (and (not modified) (buffer-modified-p) (set-buffer-modified-p nil))
      (if (and font-lock-verbose
	       (>= (- end start) font-lock-message-threshold))
	  (message "Fontifying %s... done" (buffer-name))))))

(defun twelf-font-highlight (start end face allow-overlap-p)
  "Highlight region between START and END with FONT.
If already highlighted and ALLOW-OVERLAP-P is nil, don't highlight."
  (or (= start end)
      ;;(if allow-overlap-p nil (font-lock-any-faces-p start (1- end)))
      ;; different in XEmacs 19.16?  font-lock-any-faces-p subtracts 1.
      (if allow-overlap-p nil (font-lock-any-faces-p start end))
      (font-lock-set-face start end face)))

(defun twelf-font-find-delimited-comment (limit)
  "Find a delimited Twelf comment and return (START . END), nil if none."
  (let ((comment-level nil)
	(comment-start nil))
    (if (search-forward "%{" limit t)
	(progn
	  (setq comment-start (- (point) 2))
	  (setq comment-level 1)
	  (while (and (> comment-level 0)
		      (re-search-forward "\\(%{\\)\\|\\(}%\\)"
					 limit 'limit))
	    (cond
	     ((match-beginning 1) (setq comment-level (1+ comment-level)))
	     ((match-beginning 2) (setq comment-level (1- comment-level)))))
	  (cons comment-start (point)))
      nil)))

;; doesn't work yet with LIMIT!!!
;; this should never be done in incremental-highlighting mode
(defun twelf-font-find-decl (limit)
  "Find an Twelf constant declaration and return (START . END), nil if none."
  (let (start
	end
	;; Turn off error messages
	(id (twelf-font-next-decl nil nil)))
    ;; ignore limit for now because of global buffer restriction
    (if (null id) ; (or (null id) (> (point) limit))
	nil
      (skip-chars-backward *whitespace*)
      (setq end (point))
      ;;(beginning-of-line 1)
      (backward-char (length id))
      (setq start (point))
      (twelf-font-end-of-par)
      (cons start end))))

(defun twelf-font-find-binder (var-pattern limit occ-face)
  "Find Twelf binder whose bound variable matches var-pattern.
Returns (START . END) if found, NIL if there is none before LIMIT.
Binders have the form [x],[x:A],{y},{y:A}.
As a side-effect, it highlights all occurrences of the bound
variable using the variable OCC-FACE."
  (let (start
	end
	par-end
	scope-start
	scope-end
	word
	(found nil))
    ;;; At the moment, ignore limit since restriction is done globally
    ;; (save-restriction
    ;; (narrow-to-region (point) limit)
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
	  ;; disable so that module expressions are more likely
	  ;; to be highlighted correctly.   Thu May 24 2001 -fp
	  ;;(skip-chars-forward *whitespace*)
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
	(setq par-end (point))
	(goto-char end)
	(condition-case nil (up-list 1)	; end of quantifier
	  (error (goto-char par-end)))
	(setq scope-start (min (point) par-end))
	(condition-case nil (up-list 1)	; end of scope
	  (error (goto-char par-end)))
	(setq scope-end (min (point) par-end))
	(goto-char scope-start)
	(while
	    ;; speed here???
	    (search-forward-regexp (concat "\\<" (regexp-quote word) "\\>")
				   scope-end 'limit)
	  ;; Check overlap here!!! --- current bug if in comment
	  (if (font-lock-any-faces-p (match-beginning 0) (match-end 0))
	      ;; no overlap --- ignore comments which are fontified already
	      nil
	    (font-lock-set-face (match-beginning 0) (match-end 0)
				occ-face)))
	(goto-char end)
	(cons start end)))
  ;;)
  )

(defun twelf-font-find-parm (limit)
  "Find bound Twelf parameters and return (START . END), NIL if none.
Also highlights all occurrences of the parameter.
For these purposes, a parameter is a bound, lower-case identifier."
  (twelf-font-find-binder "\\<[-a-z!&$^+/\\<=>?@~|#*`;,]\\w*\\>"
			limit 'twelf-font-parm-face))

(defun twelf-font-find-evar (limit)
  "Find bound Twelf existential variable return (START . END), NIL if none.
Also highlights all occurrences of the existential variable.
For these purposes, an existential variable is a bound, upper-case identifier."
  (twelf-font-find-binder "\\<[A-Z_]\\w*\\>"
			limit 'twelf-font-evar-face))

; next two are now in twelf.el
;(define-key twelf-mode-map "\C-c\C-l" 'twelf-font-fontify-decl)
;(define-key twelf-mode-map "\C-cl" 'twelf-font-fontify-buffer)

(provide 'twelf-font)
