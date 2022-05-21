" Vim syntax file
" Language:	Tethys
" Maintainer:	tbmreza <rezahandzalah 'at' gmail com>
" Last Change:	2022 May 21

if exists("b:current_syntax")
  finish
endif

syn match   tethysComment "\v#.*$"

syn region  tethysString start=+"+ end=+"+ skip=+\\\\\|\\"+ contains=@Spell
syn match   tethysNumber "\<\d\+\>"                           " integer
syn match   tethysNumber "\<\d\+\.\d*\%([eE][-+]\=\d\+\)\=\>" " float, with dot, optional exp
syn match   tethysNumber "\.\d\+\%([eE][-+]\=\d\+\)\=\>"      " float, starts with a dot, optional exp
syn match   tethysNumber "\<\d\+[eE][-+]\=\d\+\>"             " float, without dot, with exp

syn keyword tethysFunction println map rangeI divides intToString
syn match   tethysFunction "\h\w*" display contained

syn keyword tethysStatement   def nextgroup=tethysFunction skipwhite
syn keyword tethysConditional if then else
syn keyword tethysRepeat      each
syn match   tethysOperator    "\\"
syn match   tethysOperator    "\."
syn match   tethysOperator    ":"
syn match   tethysOperator    "="
syn match   tethysOperator    "\(forall\>\|->\)"

syn match   tethysType "()"
syn keyword tethysType Int List String

hi link tethysComment     Comment
hi link tethysString      String
hi link tethysNumber      Number
hi link tethysFunction    Function
hi link tethysStatement   Statement
hi link tethysConditional Conditional
hi link tethysRepeat      Repeat
hi link tethysOperator    Operator
hi link tethysKeyword     Keyword
hi link tethysType        Type

let b:current_syntax = "tethys"
