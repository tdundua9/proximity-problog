:- module(proximity_problog_main, [main/0]).

:- use_module('translator.pl',
              [translate_file/2]).

:- use_module(library(readutil)).

:- initialization(main, main).


main :-
    nl,
    writeln('=========================================='),
    writeln(' Proximity-Based ProbLog Translator'),
    writeln('=========================================='),
    nl,
    translator_loop.


translator_loop :-
    writeln('Enter the name of the .plp program'),
    writeln('(or type quit to exit):'),
    write('> '),
    flush_output,

    read_line_to_string(user_input, InputString),
    normalize_space(string(InputText), InputString),
    handle_input(InputText).


handle_input("quit") :-
    writeln('Translator closed.').

handle_input("exit") :-
    writeln('Translator closed.').

handle_input("") :-
    writeln('Error: no file name was entered.'),
    nl,
    translator_loop.

handle_input(InputText) :-
    atom_string(InputFile, InputText),
    process_file(InputFile),
    nl,
    translator_loop.


process_file(InputFile) :-
    (   exists_file(InputFile)
    ->  check_plp_extension(InputFile)
    ;   format(
            user_error,
            'Error: the file "~w" does not exist.~n',
            [InputFile]
        )
    ).


check_plp_extension(InputFile) :-
    (   file_name_extension(Base, Extension, InputFile),
        downcase_atom(Extension, plp)
    ->  file_name_extension(Base, pl, OutputFile),
        translate_program(InputFile, OutputFile)
    ;   writeln(
            user_error,
            'Error: the input file must have the .plp extension.'
        )
    ).


translate_program(InputFile, OutputFile) :-
    format('Translating "~w"...~n', [InputFile]),
    catch(
        run_translation(InputFile, OutputFile),
        Error,
        handle_error(Error)
    ).


run_translation(InputFile, OutputFile) :-
    (   translate_file(InputFile, OutputFile)
    ->  nl,
        writeln('Translation completed successfully.'),
        format('Input:  ~w~n', [InputFile]),
        format('Output: ~w~n', [OutputFile])
    ;   writeln(
            user_error,
            'Translation failed: translate_file/2 returned false.'
        )
    ).


handle_error(Error) :-
    nl,
    writeln(user_error, 'Translation failed with an error:'),
    print_message(error, Error).
