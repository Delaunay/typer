;;; typer-mode.el --- Typer major mode

;; Copyright (C) 2011-2016  Free Software Foundation, Inc.

;; Author: Stefan Monnier <monnier@iro.umontreal.ca>
;; Keywords: 

;; This file is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.

;; This file is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs.  If not, see <http://www.gnu.org/licenses/>.  */

;;; Commentary:

;; 

;;; Code:

(require 'smie)

(defgroup typer-mode ()
  "Major mode for Typer files."
  :group 'tools)

(defvar typer-mode-map
  (let ((map (make-sparse-keymap)))
    map)
  "Keymap for `typer-mode'.")

(easy-menu-define typer-mode-menu typer-mode-map
  "Menu for `typer-mode'."
  '("Typer"
    ))

(defvar typer-mode-syntax-table
  (let ((st (make-syntax-table)))
    (modify-syntax-entry ?% "<" st)
    (modify-syntax-entry ?\n ">" st)
    (modify-syntax-entry ?\" "\"" st)
    (modify-syntax-entry ?\\ "\\" st)
    (modify-syntax-entry ?\{ "(}" st)
    (modify-syntax-entry ?\} "){" st)
    st)
  "Syntax table for `typer-mode'.")

(defvar typer-font-lock-keywords
  '(("deftoken[ \t]+\\([^ \t\n]+\\)" (1 font-lock-function-name-face))
    ("^\\([^() \t]+\\)[ \t]" (1 font-lock-function-name-face))
    )
  "Keyword highlighting specification for `typer-mode'.")

(defvar typer-imenu-generic-expression
  '(("Special tokens" "^deftoken[ \t]+\\([^\t\n ]+\\)" 1)
    ;; (nil "^function[ \t]+\\(\\(\\sw\\|\\s_\\)+\\)" 1)
    )
  "Regex patterns for the index menu of `typer-mode'.")

(defvar typer-outline-regexp "(\\|;;;+"
  "Regexp for `outline-minor-mode' in `typer-mode'.")

;; Abbreviations and Skeletons

;; (define-skeleton typer-insert-if
;;   "Typer mode skeleton for if..then expressions."
;;   nil
;;   "if " _ \n "then " _ \n "else " _ \n "fi" \n)

;; (define-skeleton typer-insert-begend
;;   "Typer mode skeleton for begin<x>...end<x> expressions."
;;   "Block name: "
;;   "begin<" str ">" \n _ \n "end<" str ">" \n)

(define-abbrev-table 'typer-mode-abbrev-table
  '())

(defvar typer-smie-grammar
  (smie-prec2->grammar
   (smie-merge-prec2s
    (smie-bnf->prec2
     '((id)
       (exp ("(" exp ")")
            (exp "->" exp) (exp "=>" exp) (exp "≡>" exp)
            ("let" decls "in" exp)
            (exp ":" exp)
            ;; ("[" exp "]")
            ("lambda" simple_arg "->" exp)
            ("lambda" simple_arg "=>" exp)
            ("lambda" simple_arg "≡>" exp)
            ("case" exp-branches)
            ;; ("letrec" decl "in" exp)
            ;; ("if" exp "then" exp "else" exp)
            )
       (simple_arg (id) ("(" typed_arg ")"))
       (typed_arg (id ":" exp))
       (formal_arg (id) ("(" typed_formal_arg ")"))
       (typed_formal_arg (id ":" exp) (id "::" exp) (id ":::" exp))
       (pattern (id) (id ":" exp))
       (decls (decls ";" decls) (decl))
       (decl (id ":" exp) (exp "=" exp) ("type" inductive_branches))
       (inductive_branches (exp) (inductive_branches "|" inductive_branches))
       (explicit-arg (id ":=" exp) (id ":-" exp) (id ":≡" exp))
       (exp-branches (exp "|" branches))
       (branches (branches "|" branches) (pattern "=>" exp)))
     '((assoc ";")
       (nonassoc "in" "case")
       (assoc "|")
       ;; Precedence of ":" wrt "->" is not very clear:
       ;; - I think we want "a : b -> c" to parse as "a : (b -> c)".
       ;; - But it would be nice to allow "lambda x : t -> e" for
       ;;   "lambda (x : t) -> e".
       ;; - but what about "a : b : c".  Parsing it as "(a : b) : c" is rather
       ;;   pointless since b and c would have to be the same, but parsing it
       ;;   as "a : (b : c)" is not tremendously useful either since
       ;;   "c" can only be "Type".
       ;; - what about "a -> b : c"?  For both parses "c" can only be "Type".
       ;; - what about "lambda x -> e : c"?  Here both alternatives make sense.
       ;;   FWIW Coq gives lower precedence to ":", so "a -> b : c" is parsed
       ;;   as "(a -> b) : c".
       (assoc ":")                      ;Should this be left or right?
       (right "->" "=>" "≡>")
       )
     )
    ;; Precedence of "=" is tricky as well.  Cases to consider:
    ;; - "x : e1 = e2"
    ;; - "nat = (A : Type) ≡> A -> (A -> A) -> A"
    ;; - "f x = e : t"
    (smie-precs->prec2
     '((assoc ";")
       (assoc ",")
       (left "||")
       (left "&&")
       (nonassoc "==" "<" ">" "<=" ">=" "!=")
       (left "+" "-")
       ;; (assoc "*") ;; Needs to be assoc (and hence alone) for tuples.
       (left "*" "/")
       (right "^")))
    )))

(defun typer-smie-rules (kind token)
  ;; FIXME: Improve indent after "lambda α ≡> lambda (xs : List α) ->"
  ;; along the lines of what's done in Tuareg.
  (pcase (cons kind token)
    (`(:before . "|") (smie-rule-parent))
    ))

;;;###autoload
(add-to-list 'auto-mode-alist '("\\.typer\\'" . typer-mode))
;;;###autoload
(add-to-list 'auto-coding-alist '("\\.typer\\'" . utf-8))

;;;###autoload
(define-derived-mode typer-mode prog-mode "Typer"
  "A major mode for editing Typer files."
  (set (make-local-variable 'comment-start) "% ")
  (set (make-local-variable 'comment-add) 1)
  ;; (set (make-local-variable 'comment-start-skip) "#+\\s-*")
  (set (make-local-variable 'font-lock-defaults)
       '(typer-font-lock-keywords))
  (when buffer-file-name
    (set (make-local-variable 'compile-command)
         (concat "./typer " (shell-quote-argument
                             (file-relative-name buffer-file-name)))))
  (smie-setup typer-smie-grammar #'typer-smie-rules)
  ;; (set (make-local-variable 'compilation-first-column) 0)
  (set (make-local-variable 'compilation-error-screen-columns) nil)
  (set (make-local-variable 'imenu-generic-expression)
       typer-imenu-generic-expression)
  (set (make-local-variable 'outline-regexp) typer-outline-regexp)
  (easy-menu-add typer-mode-menu)
  )

(provide 'typer-mode)
;; arch-tag: b5d7a461-b1bc-4f32-b3b7-cad11d95017d
;;; typer-mode.el ends here
