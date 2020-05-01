" Vim syntax file
" Language:     ITT
" Maintainer:   Matus Tejiscak <ziman@functor.sk>
" Last Change:  1 May 2020

if exists("b:current_syntax")
	finish
endif
let b:current_syntax = 'itt'

syntax clear

syn keyword ttData data
syn keyword ttKeyword forall
syn keyword ttBody postulate foreign constructor

syn match ttOperator  "\~>\|->\|\\\|="
syn match ttDelimiter "[.,}{)(]\|\[\|\]"
syn match ttForcedCtor "{\i\+}"

syn match ttBinding   "\i\+\s*:[IELR]\?" contains=ttBoundName,ttColon
syn match ttColon     ":[IELR]\?" contained
syn match ttBoundName "\i\+" contained
syn match ttNumber "\<[0-9]\+\>"

syn match ttLineComment "---*\([^-!#$%&\*\+./<=>\?@\\^|~].*\)\?$" contains=ttTodo,@Spell
syn region ttBlockComment start="{-" end="-}" contains=ttBlockComment,ttTodo,@Spell
syn keyword ttTodo TODO FIXME XXX HACK contained

syn region ttString start=+"+ skip=+\\\\\|\\"+ end=+"+ contains=@Spell

highlight link ttData    Type
highlight link ttKeyword Keyword
highlight link ttBody    PreProc
highlight link ttDelimiter Delimiter
highlight link ttBoundName Identifier
highlight link ttColon     Delimiter
highlight link ttForcedCtor Delimiter
highlight link ttNumber Number
highlight link ttLineComment Comment
highlight link ttBlockComment Comment
highlight link ttTodo Todo
highlight link ttString String
highlight link ttOperator Operator
