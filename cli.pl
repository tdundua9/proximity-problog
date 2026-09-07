:- use_module('translator.pl', [translate_file/2]).
:- initialization(main, main).

main(Argv) :-
    ( Argv = [In,Out]
    -> catch(translate_file(In,Out), E,
             ( print_message(error,E), halt(1) ))
    ;  format(user_error, 'Usage: swipl cli.pl -- IN.plp OUT.pl~n', []),
       halt(1)
    ).
