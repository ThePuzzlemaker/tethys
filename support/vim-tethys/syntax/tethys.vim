" Vim syntax file
" Language:	Tethys
" Maintainer:	tbmreza <rezahandzalah 'at' gmail com>
" Last Change:	2022 May 21

if exists("b:current_syntax")
  finish
endif

syn keyword tethysKeyword  def if else
syn keyword tethysFunction map

syn match tethysComment  "\v#.*$"
syn match tethysOperator "\\"
syn match tethysOperator "\."
syn match tethysOperator ":"
syn match tethysOperator "="
syn match tethysOperator "\(forall\>\|->\)"

hi link tethysKeyword  Keyword
hi link tethysFunction Function
hi link tethysComment  Comment
hi link tethysOperator Operator

let b:current_syntax = "tethys"
