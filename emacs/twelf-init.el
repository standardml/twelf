;;; Begin Twelf mode setup

;; Extend emacs load path, if necessary
(cond ((not (member (concat twelf-root "emacs") load-path))
       (setq load-path (cons (concat twelf-root "emacs") load-path))))

;; Autoload libraries when Twelf-related major modes are started.
(autoload 'twelf-mode "twelf" "Major mode for editing Twelf source." t)
(autoload 'twelf-server "twelf" "Run an inferior Twelf server." t)
(autoload 'twelf-sml "twelf" "Run an inferior Twelf-SML process." t)
(autoload 'twelf-info "twelf" "Browse Twelf User's Guide." t)

;; Switch buffers to Twelf mode based on filename extension,
;; which is one of .elf, .quy, .thm, or .cfg.
(setq auto-mode-alist
      (cons '("\\.elf$" . twelf-mode)
	    (cons '("\\.quy$" . twelf-mode)
		  (cons '("\\.thm$" . twelf-mode)
			(cons '("\\.cfg$" . twelf-mode)
			      auto-mode-alist)))))

;; Default Twelf server program location
(setq twelf-server-program
      (concat twelf-root "bin/twelf-server"))

;; Default Twelf SML program location
(setq twelf-sml-program
      (concat twelf-root "bin/twelf-sml"))

;; Default documentation location (in info format)
(setq twelf-info-file
      (concat twelf-root "doc/info/twelf.info"))

;; Automatically highlight Twelf sources using font-lock
(add-hook 'twelf-mode-hook 'twelf-font-fontify-buffer)

;;; End Twelf mode setup
