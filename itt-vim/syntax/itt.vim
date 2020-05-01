" Vim syntax file
" Language:     ITT
" Maintainer:   Matus Tejiscak <ziman@functor.sk>
" Last Change:  1 May 2020

if exists("b:current_syntax")
	finish
endif
let b:current_syntax = 'itt'

syntax clear

syn match ttTypeDecl "[a-zA-Z][a-zA-z0-9_']*\s\+[:\\]"
  \ contains=ttIdentifier,ttLambda

syn region ttParens matchgroup=ttDelimiter start="(" end=")" contains=TOP
syn region ttForcedPattern matchgroup=ttDelimiter start="\[" end="]" contains=TOP
syn region ttClauses matchgroup=ttDelimiter start="{" end="}" fold
 \ contains=ALLBUT,ttClauses

syn keyword ttData data
syn keyword ttKeyword forall contained
syn keyword ttImport postulate foreign

syn match ttOperator "\$\|=\|\~>" contained
syn match ttLambda "\\" contained
syn match ttNumber "\<[0-9]\+\>\|\<0[xX][0-9a-fA-F]\+\>\|\<0[oO][0-7]\+\>" contained
syn match ttDelimiter  "[,.]\|->" contained
"syn match ttType "\<[A-Z][a-zA-Z0-9_']*\>"
syn keyword ttTodo TODO FIXME XXX HACK contained
syn match ttLineComment "---*\([^-!#$%&\*\+./<=>\?@\\^|~].*\)\?$" contains=ttTodo,@Spell
syn region ttBlockComment start="{-" end="-}" contains=ttBlockComment,ttTodo,@Spell
syn match ttIdentifier "[a-zA-Z][a-zA-z0-9_']*" contained
syn match ttForcedCtor "{[a-zA-Z][a-zA-z0-9_']*}" contained
syn region ttString start=+"+ skip=+\\\\\|\\"+ end=+"+ contains=@Spell
syn match ttColon ":[IELR]\?" contained

highlight link ttIdentifier Identifier
highlight link ttForcedCtor    Delimiter
highlight link ttForcedPattern Delimiter
highlight link ttNumber Number
highlight link ttDelimiter Delimiter
"highlight link ttType Include
highlight link ttLineComment Comment
highlight link ttBlockComment Comment
highlight link ttTodo Todo
highlight link ttKeyword Keyword
highlight link ttString String
highlight link ttColon Delimiter
highlight link ttImport Type
highlight link ttLambda Keyword
highlight link ttData Type
highlight link ttOperator Operator
highlight link ttPrefix Include
