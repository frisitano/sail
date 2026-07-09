;;; sail-mode.el --- Major mode for editing .sail files -*- lexical-binding: t; -*-

;; Copyright (C) 2013-2018 The Sail Authors
;;
;; Author: The Sail Authors
;; URL: http://github.com/rems-project/sail
;; Package-Requires: ((emacs "25"))
;; Version: 0.0.1
;; Keywords: language

;; This file is not part of GNU Emacs.

;;; License:

;; 2-Clause BSD License (See LICENSE file in Sail repository)

;;; Commentary:

;; This mode is only compatible with new, recent of the new Sail on the "sail2" branch.

;;; Code:

(require 'easymenu)
(require 'subr-x)
(require 'url-util)

(defgroup sail nil
  "Major mode and language-server integration for Sail."
  :group 'languages)

(defcustom sail-lsp-executable "sail_lsp"
  "Executable used for Sail language-server support."
  :type 'string
  :group 'sail)

(defcustom sail-lsp-arguments '("--stdio")
  "Arguments passed to `sail-lsp-executable'."
  :type '(repeat string)
  :group 'sail)

(defcustom sail-lsp-auto-start nil
  "When non-nil, start `sail_lsp' automatically in Sail source buffers.

This uses `lsp-deferred' when lsp-mode is loaded, otherwise
`eglot-ensure' when Eglot is loaded."
  :type 'boolean
  :group 'sail)

(defcustom sail-lsp-c-output nil
  "Generated C implementation file used for Sail-to-C navigation."
  :type '(choice (const :tag "Auto-discover" nil) file)
  :group 'sail)

(defcustom sail-lsp-c-map nil
  "Generated C sidecar JSON file used for Sail-to-C navigation."
  :type '(choice (const :tag "Auto-discover" nil) file)
  :group 'sail)

(defcustom sail-lsp-docinfo nil
  "Documentation info JSON file used for hover and documentation display."
  :type '(choice (const :tag "Auto-discover" nil) file)
  :group 'sail)

(defcustom sail-lsp-artifact-index nil
  "Sail LSP artifact manifest, conventionally sail.lsp.json."
  :type '(choice (const :tag "Auto-discover" nil) file)
  :group 'sail)

(defcustom sail-lsp-sail-executable nil
  "Sail compiler executable used by `sail_lsp' for diagnostics and formatting."
  :type '(choice (const :tag "Default sail on PATH" nil) file)
  :group 'sail)

(defcustom sail-lsp-project-file nil
  "Sail project file used for compiler-backed diagnostics."
  :type '(choice (const :tag "Current file only" nil) file)
  :group 'sail)

(defcustom sail-lsp-project-modules nil
  "Project module names used for compiler-backed diagnostics."
  :type '(repeat string)
  :group 'sail)

(defcustom sail-lsp-project-all-modules t
  "When non-nil, check all project modules when no explicit modules are set."
  :type 'boolean
  :group 'sail)

(defcustom sail-lsp-diagnostics-enable t
  "When non-nil, enable compiler-backed diagnostics from `sail_lsp'."
  :type 'boolean
  :group 'sail)

(defvar sail-mode-hook nil)

(defvar sail-project-mode-hook nil)

(add-to-list 'auto-mode-alist '("\\.sail\\'" . sail-mode))

(add-to-list 'auto-mode-alist '("\\.sail_project\\'" . sail-project-mode))

(defconst sail-keywords
  '("val" "outcome" "function" "type" "struct" "union" "enum" "let" "var" "if" "then" "by"
    "else" "match" "in" "return" "register" "ref" "forall" "operator" "effect" "config"
    "overload" "cast" "sizeof" "constant" "constraint" "default" "assert" "newtype" "from"
    "pure" "impure" "monadic" "infixl" "infixr" "infix" "scattered" "end" "try" "catch" "and" "to" "private"
    "throw" "clause" "as" "repeat" "until" "while" "do" "foreach" "bitfield" "when"
    "mapping" "where" "with" "implicit" "instantiation" "impl" "forwards" "backwards"))

(defconst sail-project-keywords
  '("after" "before" "directory" "else" "file" "files" "if" "default" "module" "optional" "requires" "then" "variable"))

(defconst sail-kinds
  '("Int" "Type" "Order" "Bool" "inc" "dec"
    "barr" "depend" "rreg" "wreg" "rmem" "rmemt" "wmv" "wmvt" "eamem" "wmem"
    "exmem" "undef" "unspec" "nondet" "escape" "configuration"))

(defconst sail-types
  '("vector" "bitvector" "int" "nat" "atom" "range" "unit" "bit" "real" "list" "bool" "string" "string_literal" "bits" "option" "result"))

(defconst sail-special
  '("_prove" "_not_prove" "create" "kill" "convert" "undefined"
    "$define" "$include" "$ifdef" "$ifndef" "$iftarget" "$else" "$endif" "$option" "$optimize" "$non_exec"
    "$latex" "$property" "$counterexample" "$suppress_warnings" "$assert" "$sail_internal" "$target_set"))

(defconst sail-font-lock-keywords
  `(("$\\[[a-zA-Z_]+[^]]*\\]" . font-lock-preprocessor-face)
    (,(regexp-opt sail-keywords 'symbols) . font-lock-keyword-face)
    (,(regexp-opt sail-kinds 'symbols) . font-lock-builtin-face)
    (,(regexp-opt sail-types 'symbols) . font-lock-type-face)
    (,(regexp-opt sail-special 'symbols) . font-lock-preprocessor-face)
    ("~" . font-lock-negation-char-face)
    ("\\(::\\)<" 1 font-lock-keyword-face)
    ("@" . font-lock-preprocessor-face)
    ("<->" . font-lock-negation-char-face)
    ("\'[a-zA-Z0-9_]+" . font-lock-variable-name-face)
    ("\\([a-zA-Z0-9_]+\\)(" 1 font-lock-function-name-face)
    ("function \\([a-zA-Z0-9_]+\\)" 1 font-lock-function-name-face)
    ("impl \\([a-zA-Z0-9_]+\\)" 1 font-lock-function-name-face)
    ("event \\([a-zA-Z0-9_]+\\)" 1 font-lock-function-name-face)
    ("val \\([a-zA-Z0-9_]+\\)" 1 font-lock-function-name-face)
    ("$target_set \\([a-zA-Z0-9_]+\\)" 1 font-lock-keyword-face)
    ("$include \\(<.+>\\)" 1 font-lock-string-face)
    ("$include \\(\".+\"\\)" 1 font-lock-string-face)
    ("\\_<\\([0-9]+\\|0b[0-9_]+\\|0x[0-9a-fA-F_]+\\|true\\|false\\|bitone\\|bitzero\\)\\_>\\|()" . font-lock-constant-face)))

(defconst sail-project-font-lock-keywords
  `((,(regexp-opt sail-project-keywords 'symbols) . font-lock-keyword-face)
    ("\\([a-zA-Z0-9_]+\\)[[:space:]]*{" 1 font-lock-function-name-face)
    ("\\.\\." . font-lock-string-face)
    ("$[a-zA-Z0-9]+" . font-lock-preprocessor-face)
    ("variable \\([a-zA-Z0-9_]+\\)" 1 font-lock-preprocessor-face)
    ("[a-zA-Z0-9_]+\\.sail" . font-lock-string-face)))

(defconst sail-mode-syntax-table
  (let ((st (make-syntax-table)))
    (modify-syntax-entry ?> "." st)
    (modify-syntax-entry ?_ "w" st)
    (modify-syntax-entry ?' "w" st)
    (modify-syntax-entry ?* ". 23n" st)
    (modify-syntax-entry ?/ ". 124b" st)
    (modify-syntax-entry ?\n "> b" st)
    st)
  "Syntax table for Sail mode")

(defun sail-mode ()
  "Major mode for editing Sail Language files"
  (interactive)
  (kill-all-local-variables)
  (set-syntax-table sail-mode-syntax-table)
  (use-local-map sail-mode-map)
  (sail-build-menu)
  (setq font-lock-defaults '(sail-font-lock-keywords))
  (setq-local comment-start-skip "\\(//+\\|/\\*+\\)\\s *")
  (setq-local comment-start "/*")
  (setq-local comment-end "*/")
  (setq major-mode 'sail-mode)
  (setq mode-name "Sail")
;;  (add-hook 'sail-mode-hook
;;	    (lambda () (add-hook 'after-save-hook 'sail-load nil 'local)))
  (run-hooks 'sail-mode-hook))

(defun sail-project-mode ()
  "Major mode for editing Sail Language files"
  (interactive)
  (kill-all-local-variables)
  (set-syntax-table sail-mode-syntax-table)
  (use-local-map sail-mode-map)
  (setq font-lock-defaults '(sail-project-font-lock-keywords))
  (setq-local comment-start-skip "\\(//+\\|/\\*+\\)\\s *")
  (setq-local comment-start "/*")
  (setq-local comment-end "*/")
  (setq major-mode 'sail-project-mode)
  (setq mode-name "Sail project")
  (run-hooks 'sail-project-mode-hook))

(defvar sail-process nil)

(defun sail-filter (proc string)
  (when (buffer-live-p (process-buffer proc))
    (with-current-buffer (process-buffer proc)
      (let ((moving (= (point) (process-mark proc))))
	(save-excursion
	  ;; Insert the text, advancing the process marker.
	  (goto-char (process-mark proc))
	  (insert string)
	  (set-marker (process-mark proc) (point)))
	(if moving (goto-char (process-mark proc)))))
    (eval (car (read-from-string string)))))

(defun sail-start ()
  "start Sail interactive mode"
  (interactive)
  (setq sail-process (start-process "sail" "Sail" "sail" "-i" "-emacs" "-no_warn"))
  (set-process-filter sail-process 'sail-filter))

(defun sail-quit ()
  "quit Sail interactive mode"
  (interactive)
  (when sail-process
    (process-send-string sail-process ":quit\n")
    (setq sail-process nil)))

(defun sail-type-at-cursor ()
  "get type at cursor"
  (interactive)
  (when sail-process
    (let ((loc (number-to-string (point))))
      (process-send-string sail-process (mapconcat 'identity `(":typeat " ,buffer-file-name " " ,loc "\n") "")))))

(defun sail-highlight-region (begin end text)
  (progn
    (remove-overlays)
    (let ((overlay (make-overlay begin end)))
      (overlay-put overlay 'face 'bold)
      (overlay-put overlay 'help-echo text)
      (message text)
      (setq mark-active nil))))

(defun sail-error-region (begin end text)
  (progn
    (let ((overlay (make-overlay begin end)))
      (overlay-put overlay 'face 'error)
      (overlay-put overlay 'help-echo text)
      (setq mark-active nil))))

(defvar sail-error-position nil)
(defvar sail-error-text nil)

(defun sail-error (l1 c1 l2 c2 text)
  (let ((begin (save-excursion
		 (goto-line l1)
		 (forward-char c1)
		 (point)))
	(end (save-excursion
	       (goto-line l2)
	       (forward-char c2)
	       (point))))
    (setq sail-error-text text)
    (setq sail-error-position begin)
    (sail-error-region begin end text)
    (message text)))

(defun sail-goto-error ()
  "Go to the next Sail error"
  (interactive)
  (if sail-error-position
      (progn
	(message sail-error-text)
	(goto-char sail-error-position))
    (message "No errors")))

(defun sail-load ()
  "load a Sail file"
  (interactive)
  (if (null sail-process)
      (error "No sail process (call sail-start)")
    (progn
      (remove-overlays)
      (setq sail-error-position nil)
      (setq sail-error-text nil)
      (process-send-string sail-process ":unload\n")
      (process-send-string sail-process (mapconcat 'identity `(":load " ,buffer-file-name "\n") "")))))

(defun sail-lsp--non-empty-string-p (value)
  "Return non-nil when VALUE is a non-empty string."
  (and (stringp value) (not (string-empty-p value))))

(defun sail-lsp--append-option (args option value)
  "Append OPTION and VALUE to ARGS when VALUE is a non-empty string."
  (if (sail-lsp--non-empty-string-p value)
      (append args (list option value))
    args))

(defun sail-lsp--configuration-arguments ()
  "Return command-line arguments derived from Sail LSP customization."
  (let ((args nil))
    (setq args (sail-lsp--append-option args "--c-output" sail-lsp-c-output))
    (setq args (sail-lsp--append-option args "--c-map" sail-lsp-c-map))
    (setq args (sail-lsp--append-option args "--docinfo" sail-lsp-docinfo))
    (setq args (sail-lsp--append-option args "--artifact-index" sail-lsp-artifact-index))
    (setq args (sail-lsp--append-option args "--sail" sail-lsp-sail-executable))
    (setq args (sail-lsp--append-option args "--project" sail-lsp-project-file))
    (dolist (module sail-lsp-project-modules)
      (when (sail-lsp--non-empty-string-p module)
        (setq args (append args (list "--module" module)))))
    (unless sail-lsp-project-all-modules
      (setq args (append args (list "--no-all-modules"))))
    (unless sail-lsp-diagnostics-enable
      (setq args (append args (list "--no-diagnostics"))))
    args))

(defun sail-lsp-command ()
  "Return the command used to start `sail_lsp'."
  (append (list sail-lsp-executable)
          sail-lsp-arguments
          (sail-lsp--configuration-arguments)))

(defun sail-lsp-enable ()
  "Start Sail language-server support with lsp-mode or Eglot."
  (interactive)
  (cond
   ((fboundp 'lsp-deferred)
    (lsp-deferred))
   ((fboundp 'eglot-ensure)
    (eglot-ensure))
   (t
    (user-error "Install and load lsp-mode or Eglot to use sail_lsp"))))

(defun sail-lsp--maybe-start ()
  "Start `sail_lsp' when `sail-lsp-auto-start' is non-nil."
  (when sail-lsp-auto-start
    (sail-lsp-enable)))

(add-hook 'sail-mode-hook 'sail-lsp--maybe-start)

(with-eval-after-load 'lsp-mode
  (add-to-list 'lsp-language-id-configuration '(sail-mode . "sail"))
  (lsp-register-client
   (make-lsp-client
    :new-connection (lsp-stdio-connection #'sail-lsp-command)
    :activation-fn (lsp-activate-on "sail")
    :major-modes '(sail-mode)
    :server-id 'sail-lsp)))

(with-eval-after-load 'eglot
  (add-to-list 'eglot-server-programs
               `(sail-mode . ,(sail-lsp-command))))

(defun sail-lsp--file-uri ()
  "Return a file URI for the current buffer."
  (unless buffer-file-name
    (user-error "Current buffer is not visiting a file"))
  (concat "file://" (expand-file-name buffer-file-name)))

(defun sail-lsp--position ()
  "Return the current point as a zero-based LSP position object."
  `(:line ,(1- (line-number-at-pos))
    :character ,(- (point) (line-beginning-position))))

(defun sail-lsp--position-params ()
  "Return LSP textDocument/position params for point."
  `(:textDocument (:uri ,(sail-lsp--file-uri))
    :position ,(sail-lsp--position)))

(defun sail-lsp--request-at-point (method)
  "Send METHOD to the active Sail language server at point."
  (cond
   ((and (bound-and-true-p lsp-mode) (fboundp 'lsp-request))
    (lsp-request method
                 (if (fboundp 'lsp--text-document-position-params)
                     (lsp--text-document-position-params)
                   (sail-lsp--position-params))))
   ((and (fboundp 'eglot-current-server) (eglot-current-server))
    (jsonrpc-request (eglot-current-server)
                     (intern (concat ":" method))
                     (sail-lsp--position-params)))
   (t
    (user-error "No active Sail language-server connection"))))

(defun sail-lsp--json-get (object key)
  "Return KEY from OBJECT across common JSON object representations."
  (cond
   ((hash-table-p object)
    (or (gethash key object)
        (gethash (substring key 1) object)
        (gethash (intern key) object)
        (gethash (intern (substring key 1)) object)))
   ((and (listp object) (keywordp (car-safe object)))
    (plist-get object (intern key)))
   ((listp object)
    (or (cdr (assoc (intern key) object))
        (cdr (assoc (substring key 1) object))
        (cdr (assoc key object))))
   (t nil)))

(defun sail-lsp--uri-to-path (uri)
  "Convert file URI to a local path."
  (if (and (stringp uri) (string-prefix-p "file://" uri))
      (url-unhex-string (substring uri 7))
    uri))

(defun sail-lsp--jump-to-location (location)
  "Open LOCATION returned by `sail_lsp'."
  (unless location
    (user-error "No location returned by sail_lsp"))
  (let* ((uri (sail-lsp--json-get location ":uri"))
         (range (sail-lsp--json-get location ":range"))
         (start (sail-lsp--json-get range ":start"))
         (line (or (sail-lsp--json-get start ":line") 0))
         (character (or (sail-lsp--json-get start ":character") 0)))
    (find-file (sail-lsp--uri-to-path uri))
    (goto-char (point-min))
    (forward-line line)
    (forward-char character)))

(defun sail-lsp-go-to-generated-c ()
  "Jump to the generated C location for the Sail identifier at point."
  (interactive)
  (sail-lsp--jump-to-location
   (sail-lsp--request-at-point "sail/generatedC")))

(defun sail-lsp-show-c-name ()
  "Show the generated C name for the Sail identifier at point."
  (interactive)
  (let* ((result (sail-lsp--request-at-point "sail/cName"))
         (c-name (sail-lsp--json-get result ":cName"))
         (sail-name (sail-lsp--json-get result ":sailName"))
         (source (sail-lsp--json-get result ":source")))
    (if c-name
        (message "%s%s%s"
                 (if sail-name (concat sail-name " -> ") "")
                 c-name
                 (if source (concat " (" source ")") ""))
      (user-error "No generated C name found at point"))))

(defun sail-lsp-show-type ()
  "Show Sail type information for the identifier or expression at point."
  (interactive)
  (let* ((result (sail-lsp--request-at-point "sail/type"))
         (name (sail-lsp--json-get result ":name"))
         (type (sail-lsp--json-get result ":type")))
    (if result
        (message "%s: %s" (or name "<expression>") (or type "No type metadata found"))
      (user-error "No Sail type information found at point"))))

(defun sail-lsp-show-documentation ()
  "Show Sail documentation for the identifier at point."
  (interactive)
  (let* ((result (sail-lsp--request-at-point "sail/documentation"))
         (markdown (sail-lsp--json-get result ":markdown")))
    (if markdown
        (with-help-window "*Sail Documentation*"
          (princ markdown))
      (user-error "No Sail documentation found at point"))))

(defvar sail-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "C-c C-s") 'sail-start)
    (define-key map (kbd "C-c C-l") 'sail-load)
    (define-key map (kbd "C-c C-q") 'sail-quit)
    (define-key map (kbd "C-c C-x") 'sail-goto-error)
    (define-key map (kbd "C-c C-c") 'sail-type-at-cursor)
    (define-key map (kbd "C-c C-e") 'sail-lsp-enable)
    (define-key map (kbd "C-c C-j") 'sail-lsp-go-to-generated-c)
    (define-key map (kbd "C-c C-n") 'sail-lsp-show-c-name)
    (define-key map (kbd "C-c C-t") 'sail-lsp-show-type)
    (define-key map (kbd "C-c C-d") 'sail-lsp-show-documentation)
    map))

(defun sail-build-menu ()
  (easy-menu-define
    sail-mode-menu (list sail-mode-map)
    "Sail Mode Menu."
    '("Sail"
      ["Start interactive" sail-start t]
      ["Quit interactive" sail-quit t]
      ["Check buffer" sail-load t]
      ["Goto next error" sail-goto-error t]
      ["Type at cursor" sail-type-at-cursor t]
      "---"
      ["Start language server" sail-lsp-enable t]
      ["Go to Generated C" sail-lsp-go-to-generated-c t]
      ["Show generated C name" sail-lsp-show-c-name t]
      ["Show language-server type" sail-lsp-show-type t]
      ["Show language-server documentation" sail-lsp-show-documentation t]))
  (easy-menu-add sail-mode-menu))

(provide 'sail-mode)

;;; sail-mode.el ends here
