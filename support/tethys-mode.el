;;; tethys-mode --- Major mode for editing Tethys files.
;;;
;;; Commentary:
;;;
;;; Code:

(defvar tethys-builtins
  '("true" "false"))

(defvar tethys-keywords
  '("def" "forall" "let" "in" "rec" "λ" "type" "enum" "if" "then" "else"))

(defvar tethys-tab-width nil
  "Tab width for `tethys-mode'.")

(defvar tethys-font-lock-defaults
  `(((":\\|->\\|\\.\\|\\\\\\|=" . font-lock-keyword-face)
     (,(regexp-opt tethys-builtins 'words) . font-lock-builtin-face)
     (,(regexp-opt tethys-keywords 'words) . font-lock-constant-face)
     ("\\<_?[A-Z][A-Za-z0-9_]*\\>" . font-lock-type-face)
     ("\\<_?[a-z][A-Za-z0-9_]*\\>" . font-lock-variable-name-face)
     ("_" . font-lock-constant-face)
     ("'[A-Za-z_][A-Za-z0-9_]*" . font-lock-type-face)
     ("[0-9]+" . font-lock-constant-face))))

(define-derived-mode tethys-mode prog-mode "Tethys"
  "Major mode for editing Tethys files."
  (setq font-lock-defaults tethys-font-lock-defaults)

  (when tethys-tab-width
    (setq tab-width tethys-tab-width))

  (setq comment-start "#")
  (setq comment-end "")

  (modify-syntax-entry ?# "< b" tethys-mode-syntax-table)
  (modify-syntax-entry ?\n "> b" tethys-mode-syntax-table))

(add-to-list 'auto-mode-alist '("\\.tys\\'" . tethys-mode))

(with-eval-after-load 'eglot
  (add-to-list 'eglot-server-programs
	       '(tethys-mode . ("tethys-debug-lsp"))))

(defgroup lsp-tethys nil
  "Customization group for `tethys-mode' lsp integration."
  :group 'lsp-mode)

(defcustom lsp-tethys-server-path
  "tethys-debug-lsp"
  "The language server executable."
  :group 'lsp-tethys
  :type 'string)

(defcustom lsp-tethys-server-args
  `()
  "The arguments for starting the language server."
  :group 'lsp-tethys
  :type '(repeat (string :Tag "Argument")))

(defun lsp-tethys--server-command ()
  "Command with arguments for starting the language server."
  (append (list lsp-tethys-server-path) lsp-tethys-server-args))

(add-to-list 'lsp-language-id-configuration '(tethys-mode . "tethys"))

(lsp-register-client
 (make-lsp-client
  :new-connection (lsp-stdio-connection (lambda () (lsp-tethys--server-command)))
  :major-modes '(tethys-mode)
  :server-id 'lsp-tethys
  ;; Fix workspace/configuration issues
  :initialized-fn (lambda (workspace)
                    (with-lsp-workspace workspace
                      (lsp--set-configuration (lsp-configuration-section "tethys"))))
  :synchronize-sections '("tethys")
  :language-id "tethys"))

(provide 'tethys-mode)

;;; tethys-mode.el ends here

