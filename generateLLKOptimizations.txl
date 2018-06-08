% Generate LL(k) Optimizations
% Kyle Lavorato
% Queen's University, Dec 2017

% Copyright 2017 Thomas Dean

% Revision history:

% 2.0 Documentation				- KPL	06 07 2018
% 2.0 Release Version			- KPL	06 06 2018
%	  All known issues resolved
% 1.1	LL(1) Bug Fix Support	- KPL	06 05 2018
% 1.0 	Initial revision 		- KPL 	12 01 2017 

% This program walks through a uniquely named SCL5 description of a protocol
% the has had LL(1) optimization annotated and searches for areas to optimize 
% the parse further with k lookahead. A type decision parse can
% be optimized if each element of the type decision has a kind/type element
% that is constrained to be a unique value in that type decision. These
% are then optimizable as when the code is generated the kind can be parsed
% and then based on the unique value of it, the type of the type decision is
% then known and can be parsed. Otherwise each type must be attempted to be
% fully parsed until the parse succeeds, indicating the correct type was found.

% Base Grammars

include "ASNOne.Grm"

% Local grammar overrides

define optimizable
	'@ 'optimizable
end define

define global
	'@ 'GLOBAL
end define

define at
	'@
end define

define value_set
	[number]
	| [id]
end define

% Annotations are added to rule names as a pair of numbers
% The first number represents the size of the kind element
% The second number represents the value that the kind element
% is constrained to possess

% To be optimizable the first numbers must match for a type
% decision and the second numbers must all be unique

% An annotation can also include the @ optimizable or
% @ global tags to indicate that the rule annotated with
% those is in fact optimizable by that optimization type
% during code generation
define annotation
	[opt at] [opt annotation_size] [opt number] [opt global] [opt optimizable] 
end define

% When checking to test if a field has the same size in a
% user defined type, we must also consider the offset of the
% field, not just the size as it is not the true first field
define annotation_size
	[opt number]
	|	'O [opt number] 'P [opt number]
end define

% Annotations are added to the rule that defines each type
% of a type decision
redefine type_rule_definition
	[decl] [opt annotation] '::= [type] [opt scl_additions]
end redefine

% Annotations are added to each type reference element of
% a type decision
redefine type_reference
	[id] [opt dotID] [opt annotation]
end redefine

define dot_rp
	'. [referenced_element]
end define

redefine referenced_element
	[referencable_primaries] [repeat dot_rp]
end redefine

redefine decl
    [id] [opt hatID] [opt global] [opt optimizable] %[opt annotation]
end redefine

redefine element_type
   [named_type] [opt position_value]
   | [named_type] 'OPTIONAL [opt position_value]
   |	 [named_type] 'DEFAULT [value] 
   | 	 [id]'COMPONENTS 'OF [id] 
end redefine

define position_value
  'POS
end define

redefine construction_assignment_statement
	[decl] '::= [type_decision] [opt scl_additions]				[NL]
end redefine

% Main rule followed by other rules in topological order

function main
	replace [program]
		P [program]

	% Global variable to hold a set of unique values in a type decision
	construct UniqueVal [repeat number]
	export UniqueVal
	
	% Global variable to hold a set of conflicting identical values in
	% a type decision
	construct ProblemVal [repeat number]
	export ProblemVal
	
	% Global variable to hold the current lookahead pass
	construct LLCount [number]
		1
	export LLCount
	
	% Global variable that is a general purpose flag
	construct generalFlag [number]
		0
	export generalFlag

	% Global flag that specifies if the lookahead has looped yet
	construct lookaheadLoopFlag [number]
		0
	export lookaheadLoopFlag
	
	% Global flag to specify if the lookahead has failed and the
	% annotation should not be added
	construct failFlag [number]
		0
	export failFlag
	
	% Global variable to hold all the unique types that have allready
	% been analyzed
	construct usedUniqueTypes [repeat id]
	export usedUniqueTypes
		_
	
	% Global variable to hold all the rule definitions in the input
	construct TPRULES [repeat rule_definition]
		_ [^ P]
	export TPRULES
	by
		P  [checkforLLOneOptimization TPRULES]
end function

% Step 1: Search through all type decision rules, searching for any that
% were not successfully optimized by the LL(1) process. These are the only
% cases that could be possibly optimized further.
rule checkforLLOneOptimization	TPRULES [repeat rule_definition]
	% Search for type decisions not marked as @ optimizable
	replace $ [construction_assignment_statement]	
		LONG [id] '^ SHORT [id] '::= '( TR [type_reference] RTR [repeat alternative_decision]') OPT [opt scl_additions]	
	% First type in the decision must have been attempted to be optimized
	% (Has annotations). For efficiency do not consider the rules that
	% LL(1) has determined have no values to switch off of.
	deconstruct TR
		ID [id] OPTID [opt dotID] '@ SZ [opt number] VL [opt number] OPGLOB [opt global] LLOne [opt optimizable]
	% First type must not have an optimizable tag as that indicates
	% it has been LL(1) optimized
	deconstruct not LLOne
		'@ 'optimizable
	where
		RTR [allHaveAnnotations]
	% Rest the lookahead counter to first pass
	import LLCount [number]
	export LLCount
		1
	% Reset the loop flag
	import lookaheadLoopFlag [number]
	export lookaheadLoopFlag
		0
	% Generate the LL(k) lookahead annotation
	construct look [repeat lookahead_block]
		_ 	[lookaheadFromLLOne TR RTR TPRULES] % Pass one is generated from LL(1) annotation
			[lookaheadRepeatPass TPRULES] % Passes 2-k are generated from the rules itself
	% Wrap the annotation in the XML header
	construct LLKBlock [optimizable_block]
		'<lookahead>
		look
		'</lookahead>
	deconstruct OPT
		GR [opt encoding_grammar_indicator] 
		SZB [opt size_markers_block] 
		TRB [opt transfer_rules_block]
		CB [opt constraints_block] 
	% Add the lookahead block to the end of the rule
	construct NewOPT [opt scl_additions]
		GR
		SZB
		TRB
		CB
		LLKBlock
	by
		LONG '^ SHORT '::= '( TR RTR ') NewOPT
end rule

% Match everly element of a set of [alternative_decision] to
% a pattern that contains annotations but not optimizable
rule allHaveAnnotations
	match $ [alternative_decision]
		'| ID [id] OPTID [opt dotID] '@ SZ [opt number] VL [opt number] OPGLOB [opt global]
end rule

% Step 1.1: Generate the first pass of the lookahead annotation from
% the information created by the LL(1) process to save analysis time
function lookaheadFromLLOne	TR [type_reference] RTR [repeat alternative_decision] TPRULES [repeat rule_definition]
	replace [repeat lookahead_block]
		LA [repeat lookahead_block]
	% Create the list of types with their restricted values from the type decision annotation
	construct annotationSet [repeat switch_case]
		_ [createSwitchFromTR TR] [createSwitchFromRTR each RTR]
	% Reset the unique and problem value variables
	import UniqueVal [repeat number]
	export UniqueVal
		_
	import ProblemVal [repeat number]
	export ProblemVal
		_
	import LLCount [number]
	% Remove any of the duplicate type entries that have a value that exists in the set already
	construct passOneAnnotationSet [repeat switch_case]
		_ [remov each annotationSet]
	% Needs a second pass to get the one that makes it through before being marked as a duplicate
	construct checkedAnnotationSet [repeat switch_case]
		_ [remov2 each passOneAnnotationSet]
	deconstruct TR
		ID [id] OPTID [opt dotID] '@ SZ [number] VL [number]
	% Find the rule definition for one of the restricted types to get access to the restriction statement
	deconstruct * [rule_definition] TPRULES
		ID '^ SHORT [id] ANN [opt annotation] '::= 'SEQUENCE '{
			LE [list element_type] OC [opt ',]
		'} OP [opt scl_additions]
	% Extract all the back statements in the rule definition
	construct allBacks [repeat back_block]
		_ [^ OP]
	% Count the number of backs
	construct BackCount [number]
		_ [length allBacks]
	% Only continue if the number of backs is larger than or equal to the current pass to prevent 
	% an index error
	where
		BackCount [>= LLCount]
	% Get the back statament corresponding to our current pass
	construct currentBackStmt [repeat back_block]
		allBacks [select LLCount LLCount]
	% Get the name of the field that has a restricted value
	construct typeID [id]
		_ [backWithDot currentBackStmt] [backWithDotOR currentBackStmt] [backWithoutDot currentBackStmt]
	construct TRID [repeat id]
		ID
	% Get the all the types in the type decision
	construct messageType [repeat id]
		TRID [discoverTypes each RTR]
	% Generate the list of types that had duplicate restricted values and must be analyzed further
	construct newLevel [repeat new_level]
		_ [generateNextLevel TR RTR typeID]
	% Generate the list of fields and sizes that need to be parsed to access the restricted value
	construct requiredParse [opt required_parse]
		_ [generateRequiredParse typeID LE messageType]
	% Increment the pass count
	export LLCount
		LLCount [+ 1]
	% Append this pass to the annotation
	construct FirstLookahead [lookahead_block]
		'@ typeID
		checkedAnnotationSet
		'END requiredParse newLevel
	by
		LA [. FirstLookahead]
end function

% Helper function to create the type id and restricted value entry
% from a provided [type_reference]
function createSwitchFromTR	TR [type_reference]
	replace [repeat switch_case]
		Switch [repeat switch_case]
	deconstruct TR
		ID [id] OPTID [opt dotID] '@ SZ [number] VL [number]
	construct NewCase [switch_case]
		ID '@ VL
	by
		Switch [. NewCase]
end function

% Helper function to create the type id and restricted value entry
% from a provided [alternative_decision]
function createSwitchFromRTR 	RTR [alternative_decision]
	replace [repeat switch_case]
		Switch [repeat switch_case]
	deconstruct RTR
		'| TR [type_reference]
	deconstruct TR
		ID [id] OPTID [opt dotID] '@ SZ [number] VL [number]
	construct NewCase [switch_case]
		ID '@ VL
	by
		Switch [. NewCase]
end function

% Function to remove any duplicate entries from a list of [switch_case]'s
% by only adding value entries that have not been used already
function remov 	CASE [switch_case]
	replace [repeat switch_case]
		SC [repeat switch_case]
	deconstruct CASE
		ID [id] '@ Val [number]
	import UniqueVal [repeat number]
	% Add the case only if the value has not already been insterted
	% into UniqueVal
	where not
		UniqueVal [equalValue Val]
	% Add the used value to UniqueVal
	construct UsedVals [repeat number]
		_ [markValsUsed Val]
	export UniqueVal
		UniqueVal [. UsedVals]
	by
		SC [. CASE]
end function

% Condition function that will fail if the annotation
% under examination has a value that is not equal to
% the one in the parameter
function equalValue CaseVal [number]
	match * [number]
		CaseVal
	% If we match a used value, then add it to the duplicate set
	import ProblemVal [repeat number]
	export ProblemVal
		ProblemVal [. CaseVal]
end function

% Helper function to append a value to a list
function markValsUsed	Val [number]
	replace [repeat number]
		Vals [repeat number]
	by
		Vals [. Val]
end function

% Function to perform duplicate cleanup after the inital duplicate pass.
% The initial pass will miss the first occurance of each duplicate value
% as it wilkl only prevent additional occurances from being added.
function remov2	CASE [switch_case]
	replace [repeat switch_case]
		SC [repeat switch_case]
	deconstruct CASE
		ID [id] '@ Val [number] %[list number]
	import ProblemVal [repeat number]
	% Only add the value to the final set if it does not occur in the duplicate set
	where not
		ProblemVal [equalValue Val]
	by
		SC [. CASE]
end function

% Function to extract the restricted value name from a back statement with a DotOP
function backWithDot BACK [repeat back_block]
	replace [id]
		ID [id]
	deconstruct * [back_block] BACK
		'Back '{ TYPE [id] DOTRR [repeat dot_rp] '== VALUE [number] '}
	deconstruct * [id] DOTRR
		DOT [id]
	construct index [number]
		_ [index TYPE  "_"]
	construct finalIndex [number]
		index [- 1]
	construct typeID [id]
		TYPE [: 1 finalIndex] [+ "."] [+ DOT]
	by
		typeID
end function

% Function to extract the restricted value name from a back statement with an OR condition
function backWithDotOR BACK [repeat back_block]
	replace [id]
		ID [id]
	deconstruct * [back_block] BACK
		'Back '{ TYPE [id] DOTRR [repeat dot_rp] '== VALUE [number] '|| TYPE DOTRR '== VALUE2 [number] '}
	deconstruct * [id] DOTRR
		DOT [id]
	construct index [number]
		_ [index TYPE  "_"]
	construct finalIndex [number]
		index [- 1]
	construct typeID [id]
		TYPE [: 1 finalIndex] [+ "."] [+ DOT]
	by
		typeID
end function

% Function to extract the restricted value name from a back statement with no DotOP
function backWithoutDot BACK [repeat back_block]
	replace [id]
		ID [id]
	deconstruct * [back_block] BACK
		'Back '{ TYPE [id] '== VALUE [number] '}
	construct index [number]
		_ [index TYPE  "_"]
	construct finalIndex [number]
		index [- 1]
	construct typeID [id]
		TYPE [: 1 finalIndex]
	by
		typeID
end function

% Function to save all the types in a type decision
function discoverTypes RTR [alternative_decision]
	replace [repeat id]
		IDs [repeat id]
	deconstruct RTR
		'| RTRID [id] OPTID [opt dotID] '@ SZ [opt number] VL [opt number] OPGLOB [opt global]
	deconstruct not * IDs
		RTRID
	by
		IDs [. RTRID]
end function

% Function to generate the lookahead segment that describes the 
% types that must be analyzed in the next pass, and the duplicate
% value that they share
function generateNextLevel	TR [type_reference] RTR [repeat alternative_decision] typeID [id]
	replace [repeat new_level]
		NL [repeat new_level]
	import ProblemVal [repeat number]
	% Get a single occurance only of each duplicate restricted value
	construct UniqueProblem [repeat number]
		_ [getUniqueHelper each ProblemVal]
	% Get a list of all the types in the type decision
	construct IDSet [repeat id]
		_ [^ TR] [^ RTR]
	% Generate a [new_level] entry for each uniquely duplicated value
	construct IDList [repeat new_level]
		_ [generateConflictingValue IDSet typeID each UniqueProblem]
	by
		IDList
end function

% Helper function to append a number to a list, only if it not already in the list
function getUniqueHelper	Val [number]
	replace [repeat number]
		Vals [repeat number]
	deconstruct not * Vals
		Val
	by
		Vals [. Val]
end function

% Function to create a [new_level] entry for a specific dulpicated value
function generateConflictingValue	IDSet [repeat id] typeID [id] ProblemVal [number]
	replace [repeat new_level]
		RNL [repeat new_level]
	% Get all the type names that share this duplicated value
	construct IDList [list id]
		_ [generateConflictIDMatch ProblemVal typeID each IDSet]
	construct Level [new_level]
		IDList '@ ProblemVal
	by
		RNL [. Level]
end function

% Function to save a type name if it has a back statement restricting
% a specified field to a duplicated value
function generateConflictIDMatch	ProblemVal [number] typeID [id] ID [id]
	replace [list id]
		IDL [list id]
	% Pass the rule set down to here and search for the ID and ProblemVal in that
	import TPRULES [repeat rule_definition]
	import LLCount [number]
	% Get the rule definition for the type under test
	deconstruct * [rule_definition] TPRULES
		ID '^ SHORT [id] ANN [opt annotation] '::= 'SEQUENCE '{
			LE [list element_type] OC [opt ',]
		'} OP [opt scl_additions]
	% Extract all the back statements in the rule definition
	construct allBacks [repeat back_block]
		_ [^ OP]
	% Count the number of backs
	construct BackCount [number]
		_ [length allBacks]
	% Only continue if the number of backs is larger than or equal to the current pass to prevent 
	% an index error
	where
		BackCount [>= LLCount]
	% Get the back statament corresponding to our current pass
	construct currentBackStmt [repeat back_block]
		allBacks [select LLCount LLCount]
	% Check if the current back statement has the duplicated value as the restriction
	% The ID will be changed to correct formatting if it passes this check
	construct TYPE [id]
		ID [deconstructDotBack currentBackStmt ProblemVal] [deconstructStdBack currentBackStmt ProblemVal]
	% Append the type only if it passes the above check
	where
		TYPE [grep typeID]
	by
		IDL [, ID]
end function

% Helper function to check for a back statement with a specific value restriction
% and to format the [ID] properly if it passes for the DotOP back case.
function deconstructDotBack	BACK [repeat back_block] ProblemVal [number]
	replace [id]
		OLD [id]
	deconstruct * [back_block] BACK
		'Back '{ TYPE [id] DOTRR [repeat dot_rp] '== ProblemVal '}
	deconstruct * [id] DOTRR
		DOT [id]
	construct index [number]
		_ [index TYPE  "_"]
	construct finalIndex [number]
		index [- 1]
	construct typeID [id]
		TYPE [: 1 finalIndex] [+ "."] [+ DOT]
	by
		typeID
end function

% Helper function to check for a back statement with a specific value restriction
% and to format the [ID] properly if it passes for the standard back case.
function deconstructStdBack	BACK [repeat back_block] ProblemVal [number]
	replace [id]
		OLD [id]
	deconstruct * [back_block] BACK
		'Back '{ TYPE [id] '== ProblemVal '}
	by
		TYPE
end function

% Function to generate the list of fields and offset sizes that must be parsed to 
% reach and parse the field with the restricted value on it.
function generateRequiredParse typeID [id] LE [list element_type] messageType [repeat id]
	replace [opt required_parse]
		RP [opt required_parse]
	% Reset the general flag
	import generalFlag [number]
	export generalFlag
		0
	% Generate the list of fields and sizes
	construct parseList [list item_to_parse]
		_ [generateParseList typeID messageType each LE]
	% Wrap the parse list in the required brackets
	construct listOfParse [required_parse]
		'< parseList '>
	by
		listOfParse
end function

% Function to generate name and size information for each field in a type rule
% until reaching the field with the restricted value
function generateParseList typeID [id] messageType [repeat id] LE [element_type]
	replace [list item_to_parse]
		ItP [list item_to_parse] 
	% Only continue to add fields if we have not reached the target yet
	import generalFlag [number]
	where
		generalFlag [= 0]
	% Get the size info for any field type
	construct newItem [list item_to_parse]
		_ 	[parseInteger LE messageType]
			[parseReal LE messageType]
			[parseUserType LE messageType]
			[parseOctet LE messageType]
			[checkIfTarget typeID LE] % After parsing, check if this field is our target
	by
		ItP [, newItem]
end function

% Function to generate an [item_to_parse] entry for an integer type.
% It will also append a POS flag for any types that have a POS restriction
% on this field.
function parseInteger	ET [element_type] messageType [repeat id]
	replace [list item_to_parse]
		Old [list item_to_parse]
	% Extract the info from the field
	deconstruct ET
		LONG [id] '^ SHORT [id] 'INTEGER '(SIZE SZ [number] 'BYTES) OP [opt endian] POS [opt position_value]
	% Generate a list of types that have a POS restriction on this field
	construct posItems [list pos_flag]
		_ [generatePOSItemsInteger SHORT each messageType]
	% Construct the POS flag set
	construct posList [opt pos_flag_list]
		'{ posItems '}
	% Remove the POS flag set if it is empty
	construct posListFinal [opt pos_flag_list]
		posList [removeEmptyPosList]
	% Generate the [item_to_parse] entry
	construct New [list item_to_parse]
		SHORT '@ SZ posListFinal
	by
		New
end function

% Helper function to check the type rule definition for a specific type
% to determine if it has a POS restriction on a specific field.
function generatePOSItemsInteger ETShort [id] messageType [id]
	replace [list pos_flag]
		Flags [list pos_flag]
	import TPRULES [repeat rule_definition]
	% Get the type rule definition for the type under inspection
	deconstruct * [rule_definition] TPRULES
		messageType '^ SHORT [id] ANN [opt annotation] '::= 'SEQUENCE '{
			LE [list element_type] OC [opt ',]
		'} OP [opt scl_additions]
	% Get the element of the specified field
	deconstruct * [element_type] LE
		LONG [id] '^ ETShort 'INTEGER '(SIZE SZ [number] 'BYTES) OPEND [opt endian] POSIT [opt position_value]
	% Continue only if it has a POS restriction
	deconstruct POSIT
		'POS
	% Append this type to the list
	construct newFlag [pos_flag]
		messageType
	by
		Flags [, newFlag]
end function

% Helper function to erase a POS flag list if it is empty
function removeEmptyPosList
	replace [opt pos_flag_list]
		'{ PosList [list pos_flag] '}
	deconstruct not * PosList
		AnyElement [id]
	by
		_
end function

% Function to generate an [item_to_parse] entry for a real type.
% It will also append a POS flag for any types that have a POS restriction
% on this field.
function parseReal	ET [element_type] messageType [repeat id]
	replace [list item_to_parse]
		Old [list item_to_parse]
	% Extract the info from the field
	deconstruct ET
		LONG [id] '^ SHORT [id] 'REAL '(SIZE SZ [number] 'BYTES) OP [opt endian] POS [opt position_value]
	% Generate a list of types that have a POS restriction on this field
	construct posItems [list pos_flag]
		_ [generatePOSItemsReal SHORT each messageType]
	% Construct the POS flag set
	construct posList [opt pos_flag_list]
		'{ posItems '}
	% Remove the POS flag set if it is empty
	construct posListFinal [opt pos_flag_list]
		posList [removeEmptyPosList]
	% Generate the [item_to_parse] entry
	construct New [list item_to_parse]
		SHORT '@ SZ posListFinal
	by
		New
end function

% Helper function to check the type rule definition for a specific type
% to determine if it has a POS restriction on a specific field.
function generatePOSItemsReal ETShort [id] messageType [id]
	replace [list pos_flag]
		Flags [list pos_flag]
	import TPRULES [repeat rule_definition]
	% Get the type rule definition for the type under inspection
	deconstruct * [rule_definition] TPRULES
		messageType '^ SHORT [id] ANN [opt annotation] '::= 'SEQUENCE '{
			LE [list element_type] OC [opt ',]
		'} OP [opt scl_additions]
	% Get the element of the specified field
	deconstruct * [element_type] LE
		LONG [id] '^ ETShort 'REAL '(SIZE SZ [number] 'BYTES) OPEND [opt endian] POSIT [opt position_value]
	% Continue only if it has a POS restriction
	deconstruct POSIT
		'POS
	% Append this type to the list
	construct newFlag [pos_flag]
		messageType
	by
		Flags [, newFlag]
end function

% Function to generate an [item_to_parse] entry for an octet type.
% It will also append a POS flag for any types that have a POS restriction
% on this field.
function parseOctet	ET [element_type] messageType [repeat id]
	replace [list item_to_parse]
		Old [list item_to_parse]
	% Extract the info from the field
	deconstruct ET
		LONG [id] '^ SHORT [id] 'OCTET 'STRING '(SIZE SZ [number] 'BYTES) OP [opt endian] POS [opt position_value]
	% Generate a list of types that have a POS restriction on this field
	construct posItems [list pos_flag]
		_ [generatePOSItemsOctet SHORT each messageType]
	% Construct the POS flag set
	construct posList [opt pos_flag_list]
		'{ posItems '}
	% Remove the POS flag set if it is empty
	construct posListFinal [opt pos_flag_list]
		posList [removeEmptyPosList]
	% Generate the [item_to_parse] entry
	construct New [list item_to_parse]
		SHORT '@ SZ posListFinal
	by
		New
end function

% Helper function to check the type rule definition for a specific type
% to determine if it has a POS restriction on a specific field.
function generatePOSItemsOctet ETShort [id] messageType [id]
	replace [list pos_flag]
		Flags [list pos_flag]
	import TPRULES [repeat rule_definition]
	% Get the type rule definition for the type under inspection
	deconstruct * [rule_definition] TPRULES
		messageType '^ SHORT [id] ANN [opt annotation] '::= 'SEQUENCE '{
			LE [list element_type] OC [opt ',]
		'} OP [opt scl_additions]
	% Get the element of the specified field
	deconstruct * [element_type] LE
		LONG [id] '^ ETShort 'OCTET 'STRING '(SIZE SZ [number] 'BYTES) OPEND [opt endian] POSIT [opt position_value]
	% Continue only if it has a POS restriction
	deconstruct POSIT
		'POS
	% Append this type to the list
	construct newFlag [pos_flag]
		messageType
	by
		Flags [, newFlag]
end function

% Function to generate an [item_to_parse] entry for a user defined type.
% It will also append a POS flag for any types that have a POS restriction
% on this field.
function parseUserType	ET [element_type] messageType [repeat id]
	replace [list item_to_parse]
		Old [list item_to_parse]
	% Extract the info from the field
	deconstruct ET
		LONG [id] '^ SHORT [id] TYPE [id] '(SIZE 'DEFINED) OPT [opt endian] POS [opt position_value]
	% Generate a list of types that have a POS restriction on this field
	construct posItems [list pos_flag]
		_ [generatePOSItemsUserType SHORT each messageType]
	% Construct the POS flag set
	construct posList [opt pos_flag_list]
		'{ posItems '}
	% Remove the POS flag set if it is empty
	construct posListFinal [opt pos_flag_list]
		posList [removeEmptyPosList]
	% Generate the [item_to_parse] entry
	construct New [list item_to_parse]
		SHORT '@ TYPE posListFinal
	by
		New
end function

% Helper function to check the type rule definition for a specific type
% to determine if it has a POS restriction on a specific field.
function generatePOSItemsUserType ETShort [id] messageType [id]
	replace [list pos_flag]
		Flags [list pos_flag]
	import TPRULES [repeat rule_definition]
	% Get the type rule definition for the type under inspection
	deconstruct * [rule_definition] TPRULES
		messageType '^ SHORT [id] ANN [opt annotation] '::= 'SEQUENCE '{
			LE [list element_type] OC [opt ',]
		'} OP [opt scl_additions]
	% Get the element of the specified field
	deconstruct LE
		LONG [id] '^ ETShort TYPE [id] '(SIZE 'DEFINED) OPEND [opt endian] POSIT [opt position_value]
	% Continue only if it has a POS restriction
	deconstruct POSIT
		'POS
	% Append this type to the list
	construct newFlag [pos_flag]
		messageType
	by
		Flags [, newFlag]
end function

% Function to update the general flag global if we have reached our
% target field that needed to be parsed
function checkIfTarget typeID [id] ET [element_type]
	replace [list item_to_parse]
		Unused [list item_to_parse]
	% Remove the dot operator if present
	construct typeIDRevised [id]
		typeID [removeTypeIDDot]
	% Continue if this field matched the target
	deconstruct * [id] ET
		typeIDRevised
	% Update the general flag
	import generalFlag [number]
	export generalFlag
		1
	by
		Unused
end function

% Helper function to remove the field information after the '.' in
% in a DotOP field
function removeTypeIDDot
	replace [id]
		TypeID [id]
	construct index [number]
		_ [index TypeID  "."]
	construct finalIndex [number]
		index [- 1]
	construct EditedID [id]
		TypeID [: 1 finalIndex]	
	by
		EditedID
end function

% Step 1.2: Rule to recursively anayze the types from the previous
% pass' [next_level] statement to see if those types can be identified
% by a further restricted value. Analysis stops when there are no 
% remaining transfer statements
rule lookaheadRepeatPass	TPRULES [repeat rule_definition]
	replace $ [repeat lookahead_block]
		Lookahead [repeat lookahead_block]
	% Check the loop flag to see if we have reached end of analysis
	% or should we keep checking
	import lookaheadLoopFlag [number]
	where
		lookaheadLoopFlag [= 0]
	export lookaheadLoopFlag
		1	% We have attempted a lookahead; If the deconstruct fails it
			% will remain at one
	% Get the information of the previous lookahead
	construct LastLook [repeat lookahead_block]
		Lookahead [getOnlyLookahead] [getLastLookahead]
	deconstruct * [lookahead_block] LastLook
		'@ LastID [id]
		Switch [repeat switch_case]
		'END RQP [opt required_parse] NL [repeat new_level]

	%% At this point we are going to ignore the newlevel, future work can
	%% be to include it and backtrack parse those elements while keeping
	%% the rest optimized

	% Get the first [new_level] from the annotation
	deconstruct NL
		LevelOne [new_level] REST [repeat new_level]
	% Generate the next lookahead pass annotation for the [new_level]
	construct newLookaheadBlock [repeat lookahead_block]
		_ [generateAdditionalLookaheadBlock LevelOne LastID TPRULES]
	export lookaheadLoopFlag
		0	% We were successful, so lookahead again
	by
		Lookahead [. newLookaheadBlock]
end rule

% Helper function to remain constant if we only have one lookahead
% block currently in our annotation
function getOnlyLookahead
	replace [repeat lookahead_block]
		Block [repeat lookahead_block]
	construct Size [number]
		_ [length Block]
	where
		Size [= 1]
	by
		Block
end function

% Helper function to provide only the most recent lookahead block
% when we have more than one in our annotation
function getLastLookahead
	replace [repeat lookahead_block]
		Blocks [repeat lookahead_block]
	construct Size [number]
		_ [length Blocks]
	where
		Size [> 1]
	% Return the last lookahead block
	construct LastLook [repeat lookahead_block]
		_ [tail Size]
	by
		LastLook
end function

% Step 1.3: Function to generate the annotation for the next lookahead
% pass, provided with a specific [new_level]
function generateAdditionalLookaheadBlock	Level [new_level] LastParsedSHORT [id] TPRULES [repeat rule_definition]
	replace [repeat lookahead_block]
		Block [repeat lookahead_block]
	% Get the types that need to be analyzed in this next lookahead pass
	deconstruct Level
		AllRulesToCheck [list id] '@ OldVal [number]
	% Get the first type from the list
	deconstruct AllRulesToCheck
		FirstRule [id] ', RestRulesToCheck [list id]

	%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
	%% This block verifies that each rule has the next back statament %%
	%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
	import LLCount [number]
	% Get the type rule definition for the first type in the types to check
	deconstruct * [rule_definition] TPRULES
		FirstRule '^ SHORT [id] ANN [opt annotation] '::= 'SEQUENCE '{
			LE [list element_type] OC [opt ',]
		'} OP [opt scl_additions]
	% Extract all the back statements in the rule definition
	construct allBacks [repeat back_block]
		_ [^ OP]
	% Count the number of backs
	construct BackCount [number]
		_ [length allBacks]
	% Only continue if the number of backs is larger than or equal to the current pass to prevent 
	% an index error
	where
		BackCount [>= LLCount]
	% Get the back statament corresponding to our current pass
	construct currentBackStmt [repeat back_block]
		allBacks [select LLCount LLCount]
	% Get the name of the field that has a restricted value
	construct typeID [id]
		_ [backWithDot currentBackStmt] [backWithDotOR currentBackStmt] [backWithoutDot currentBackStmt]
	% Check each of the remainig types under analysis to save the
	% field in the next back statement
	construct restTypeID [repeat id]
		_ [searchForBack TPRULES each RestRulesToCheck]
	% Check that all the extracted restrictions are on the same field
	where all
		typeID [matchID each restTypeID]

	%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
	%% This block verifies that each rule matches fields up to the next back statement %%
	%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
	% Construct a list of all the fields and values for the first type
	% up to and including the field of the restricted value, otherwise
	% the offset will be different and unparsable
	construct FirstRuleValues [repeat value_set]
		_ [constructValueSet FirstRule LastParsedSHORT typeID TPRULES] %[debug]
	%% We must now construct this same set for each of the other three rules and if they all match then
	%% we meet all the conditions to create the lookahead block
	construct zero [number]
		0
	% If any of the runs of this in the each fail then pass test will be '1' indicating a fail
	construct passTest [number]
		zero [checkValueSets FirstRuleValues LastParsedSHORT typeID TPRULES each RestRulesToCheck] %[debug]
	% Continue only if we did not fail any match
	where
		passTest [= 0]

	%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
	%% This block constructs the next parts of the lookahead_block %%
	%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
	% Generate a temporary type decision annotation, annotated in the 
	% LL(1) style, as we know it is optimizable. This lets us reuse the
	% previous annotation generation rules
	construct allTempRTRForSwitch [repeat alternative_decision]
		_ [constructFirstTempRTR FirstRule currentBackStmt] [constructRestTempRTR TPRULES each RestRulesToCheck]
	% Extract the first TR from the RTR to create the type decision
	deconstruct allTempRTRForSwitch
		FirstRTR [alternative_decision] tempRTRForSwitch [repeat alternative_decision]
	deconstruct FirstRTR
		'| tempTRForSwitch [type_reference]
	% Use the same functions as Step 1.1 to generate the entries for
	% each type and restricted values
	construct annotationSet [repeat switch_case]
		_ [createSwitchFromTR tempTRForSwitch] [createSwitchFromRTR each tempRTRForSwitch]
	% Reset the unique and problem val sets as in Step 1.1
	import UniqueVal [repeat number]
	export UniqueVal
		_
	import ProblemVal [repeat number]
	export ProblemVal
		_
	% Invoke the same 2 pass system to remove any types with duplicate
	% restricted values
	construct passOneAnnotationSet [repeat switch_case]
		_ [remov each annotationSet]
	% Needs a second pass to get the one that makes it through before being marked as a duplicate
	construct checkedAnnotationSet [repeat switch_case]
		_ [remov2 each passOneAnnotationSet]

	% Get all the types from the type decision
	construct messageType [repeat id]
		_ [discoverTypes each allTempRTRForSwitch]
	% Generate the list of fields that need to be parsed to access the field
	% with the restricted value. 
	%% Since this is not the first pass, it is possible that the field with
	%% the restricted value is already parsed and we just generate an empty list
	construct requiredParse [opt required_parse]
		_ [generateRequiredParseBetween LastParsedSHORT typeID messageType LE]
		  [generateEmptyRequired LastParsedSHORT typeID messageType LE]

	% Generate the set of types that had duplicate restricted values in this
	% pass if they exist, otherwise the annotation terminates here 
	construct newLevel [repeat new_level]
		_ [generateNextLevel tempTRForSwitch tempRTRForSwitch typeID]

	% Increment the lookahead pass count
	export LLCount
		LLCount [+ 1]

	% Assemble the full pass annotation
	construct Lookahead [lookahead_block]
		'@ typeID
		checkedAnnotationSet
		'END requiredParse newLevel
	by
		Lookahead
end function

% Function to extract the field in the back statement for the current
% pass for the type specified
function searchForBack	TPRULES [repeat rule_definition] RuleID [id]
	replace [repeat id]
		IDs [repeat id]
	import LLCount [number]
	deconstruct * [rule_definition] TPRULES
		RuleID '^ SHORT [id] ANN [opt annotation] '::= 'SEQUENCE '{
			LE [list element_type] OC [opt ',]
		'} OP [opt scl_additions]
	% Extract all the back statements in the rule definition
	construct allBacks [repeat back_block]
		_ [^ OP]
	% Count the number of backs
	construct BackCount [number]
		_ [length allBacks]
	% Only continue if the number of backs is larger than or equal to the current pass to prevent 
	% an index error
	where
		BackCount [>= LLCount]
	% Get the back statament corresponding to our current pass
	construct currentBackStmt [repeat back_block]
		allBacks [select LLCount LLCount]
	% Get the name of the field that has a restricted value
	construct typeID [id]
		_ [backWithDot currentBackStmt] [backWithDotOR currentBackStmt] [backWithoutDot currentBackStmt]
	by
		IDs [. typeID]
end function

% Condition function to check if two [ID]'s are the same
function matchID	toMatch [id]
	match [id]
		toMatch
end function

% Function to construct a list of all the fields and values for the first type
% up to and including the field of the restricted value, otherwise
% the offset will be different and unparsable
function constructValueSet	RuleID [id] LastParsedSHORT [id] matchID [id] TPRULES [repeat rule_definition]
	replace [repeat value_set]
		NULL [repeat value_set]
	deconstruct * [rule_definition] TPRULES
		RuleID '^ SHORT [id] ANN [opt annotation] '::= 'SEQUENCE '{
			LE [list element_type] OC [opt ',]
		'} OP [opt scl_additions]
	% Reset the general flag
	import generalFlag [number]
	export generalFlag
		0
	% Remove allready parsed elements from LE
	construct IteratedLE [list element_type]
		_ [removeParsedElements LastParsedSHORT matchID each LE] %[debug]
	% Construct new set for each LE
	construct ValSet [repeat value_set]
		_ [getValueSet each IteratedLE]
	by
		ValSet
end function

% Helper function to remove any of the elements that have been parsed
% in previous lookahead passes from the list of fields
function removeParsedElements	LastParsedSHORT [id] matchID [id] ET [element_type]
	replace [list element_type]
		LE [list element_type]
	construct flag [id]
		LastParsedSHORT [flagDeconstructBefore LastParsedSHORT ET]
	import generalFlag [number]
	where 
		generalFlag [= 1]	% Ignore the stuff before last parsed
	where not
		ET [matchLastParsed LastParsedSHORT]	% Ignore the last parsed
	construct flag2 [id]
		matchID [flagDeconstructAfter matchID ET]
	by
		LE [, ET]
end function

% Helper function to check if we have reached our traget field
% and set the global flag
function flagDeconstructBefore	LastParsedSHORT [id] ET [element_type]
	replace [id]
		N [id]
	deconstruct * [id] ET
		LastParsedSHORT
	% Set the flag since we have reached our target
	import generalFlag [number]
	export generalFlag
		1
	by
		N
end function

% Helper function
function flagDeconstructAfter	matchID [id] ET [element_type]
	replace [id]
		N [id]
	construct index [number]
		_ [index matchID  "."]
	construct finalIndex [number]
		index [- 1]
	construct typeID [id]
		matchID [: 1 finalIndex]
	deconstruct * [id] ET
		typeID
	import generalFlag [number]
	export generalFlag
		0
	by
		N
end function

% Conditional function to match two [ID]'s
function matchLastParsed	LastParsedSHORT [id]
	match * [id]
		LastParsedSHORT
end function

% Function to determine and save the size of the field
% for the passed in [element_type]
function getValueSet	ET [element_type]
	% In that function have a function for both int and size def
	replace [repeat value_set]
		ValSet [repeat value_set]
	% Find the size
	construct Val [repeat value_set]
		_ [getValInteger ET] [getValDefined ET]
	by
		ValSet [. Val]
end function

% Function to get the size of an integer field type
function getValInteger	ET [element_type]
	replace [repeat value_set]
		NULL [repeat value_set]
	deconstruct ET
		LONG [id] '^ SHORT [id] 'INTEGER '(SIZE SZ [number] 'BYTES) OP [opt endian] POS [opt position_value]
	by
		SZ
end function

% Function to get the size of a user defined field type
function getValDefined	ET [element_type]
	replace [repeat value_set]
		NULL [repeat value_set]
	deconstruct ET
		LONG [id] '^ SHORT [id] TYPE [id] '(SIZE 'DEFINED) OPT [opt endian] POS [opt position_value]
	by
		TYPE
end function

% Function to ensure that the values for the rule under analysis
% match the values from the first rule, otherwise we cannot optimize
function checkValueSets	FirstRuleValues [repeat value_set] LastParsedSHORT [id] typeID [id] TPRULES [repeat rule_definition] RuleID [id]
	replace [number]
		N [number]
	construct RuleValues [repeat value_set]
		_ [constructValueSet RuleID LastParsedSHORT typeID TPRULES]
	where not
		FirstRuleValues [= RuleValues]
	by
		1	% If the function reaches replacement, its a failure
end function

% Function to create a temporary LL(1) style annotated [alternative_decision]
% for the type and field we know can be optimized
function constructFirstTempRTR	RuleID [id] currentBackStmt [repeat back_block]
	replace [repeat alternative_decision]
		RTR [repeat alternative_decision]
	% Create the annotated [alternative_decision]
	construct newAlt [repeat alternative_decision]
		_ [backVal RuleID currentBackStmt] [backWithORVal RuleID currentBackStmt]
	by
		RTR [. newAlt]
end function

% Helper function to construct a new annotated [alternative_decision]
% for a standard back statement
function backVal RuleID [id] BACK [repeat back_block]
	replace [repeat alternative_decision]
		ALT [repeat alternative_decision]
	% Extract the info from the back statement
	deconstruct * [back_block] BACK
		'Back '{ TYPE [id] DOTRR [repeat dot_rp] '== VALUE [number] '}
	% Construct the annotated element
	% The size element of the annotation is set to 0 accross
	% all newly generated elements to allow them to match
	% The actual size does not need to be used as matching
	% sizes has already been verified
	construct newAlt [alternative_decision]
		'| RuleID '@ 0 VALUE
	by
		_ [. newAlt]
end function

% Helper function to construct a new annotated [alternative_decision]
% for a back statement with an OR condition
function backWithORVal RuleID [id] BACK [repeat back_block]
	replace [repeat alternative_decision]
		ALT [repeat alternative_decision]
	% Extract the info from the back statement
	deconstruct * [back_block] BACK
		'Back '{ TYPE [id] DOTRR [repeat dot_rp] '== VALUE [number] '|| TYPE DOTRR '== VALUE2 [number] '}
	%% Construct a new element for each of the different value restrictions
	%% from the back statement
	% The size element of the annotation is set to 0 accross
	% all newly generated elements to allow them to match
	% The actual size does not need to be used as matching
	% sizes has already been verified
	construct newAlt1 [alternative_decision]
		'| RuleID '@ 0 VALUE
	construct newAlt2 [alternative_decision]
		'| RuleID '@ 0 VALUE2
	by
		_ [. newAlt1] [. newAlt2]
end function

% Function to create a temporary LL(1) style annotated [alternative_decision]
% for the type and field we know can be optimized
function constructRestTempRTR	TPRULES [repeat rule_definition] RuleID [id]
	replace [repeat alternative_decision]
		RTR [repeat alternative_decision]
	import LLCount [number]
	% Get the type rule definition for the type that needs the annotation
	deconstruct * [rule_definition] TPRULES
		RuleID '^ SHORT [id] ANN [opt annotation] '::= 'SEQUENCE '{
			LE [list element_type] OC [opt ',]
		'} OP [opt scl_additions]
	% Extract all the back statements in the rule definition
	construct allBacks [repeat back_block]
		_ [^ OP]
	% Count the number of backs
	construct BackCount [number]
		_ [length allBacks]
	% Only continue if the number of backs is larger than or equal to the current pass to prevent 
	% an index error
	where
		BackCount [>= LLCount]
	% Get the back statament corresponding to our current pass
	construct currentBackStmt [repeat back_block]
		allBacks [select LLCount LLCount]
	% Create the annotated [alternative_decision]
	construct newAlt [repeat alternative_decision]
		_ [backVal RuleID currentBackStmt] [backWithORVal RuleID currentBackStmt]
	by
		RTR [. newAlt]
end function

% Generate the list of items to parse between a specified start and end 
% field
function generateRequiredParseBetween startID [id] endID [id] messageType [repeat id] LE [list element_type]
	replace [opt required_parse]
		RP [opt required_parse]
	% Remove possible diffeing .[id] field for comparison
	construct revisedStart [id]
		startID [removeTypeIDDot]
	construct revisedEnd [id]
		endID [removeTypeIDDot]
	% If the start == end then we do not have to parse anything
	where not
		revisedStart [= revisedEnd]
	import generalFlag [number]
	export generalFlag
		1
	% Generate the list of fields to parse
	construct parseList [list item_to_parse]
		_ [generateParseListBetween startID endID messageType each LE]
	% Wrap the list opf fields in the correct brackets
	construct listOfParse [required_parse]
		'< parseList '>
	by
		listOfParse
end function

% Generate an empty list of items to parse if the start and end elements
% are matching as nothing needs to be parsed
function generateEmptyRequired startID [id] endID [id] messageType [repeat id] LE [list element_type]
	replace [opt required_parse]
		RP [opt required_parse]
	% Remove possible diffeing .[id] field for comparison
	construct revisedStart [id]
		startID [removeTypeIDDot]
	construct revisedEnd [id]
		endID [removeTypeIDDot]
	% If the start == end then we do not have to parse anything
	where
		revisedStart [= revisedEnd]
	construct listOfParse [required_parse]
		'< '>
	by
		listOfParse
end function

% Function to generate name and size information for each field in a type rule
% until reaching the field with the restricted value
function generateParseListBetween startID [id] endID [id] messageType [repeat id] LE [element_type]
	replace [list item_to_parse]
		ItP [list item_to_parse] 
	import generalFlag [number]
	% Reset the general flag if on the initial element
	construct newItem1 [list item_to_parse]
		_ [checkIfStart startID LE]
	% Only continue to add fields if we have not reached the target yet
	where
		generalFlag [= 0]
	% Get the size info for any field type
	construct newItem2 [list item_to_parse]
		_ 	[parseInteger LE messageType]
			[parseReal LE messageType]
			[parseUserType LE messageType]
			[parseOctet LE messageType]
			[checkIfTarget endID LE] % After parsing, check if this field is our target
	by
		ItP [, newItem2]
end function

% Helper function to reset the general flag global if the 
% passed in [element_type] matches the passed in [ID]
function checkIfStart typeID [id] ET [element_type]
	replace [list item_to_parse]
		Unused [list item_to_parse]
	construct typeIDRevised [id]
		typeID [removeTypeIDDot]
	deconstruct * [id] ET
		typeIDRevised
	import generalFlag [number]
	export generalFlag
		0
	by
		Unused
end function