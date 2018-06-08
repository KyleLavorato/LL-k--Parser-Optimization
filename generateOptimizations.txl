% Generate Header
% Ali El-Shakankiry
% Queen's University, Jan 2017

% Copyright 2017 Thomas Dean

% Revision history:

% 1.2 Documentation			- KPL	27 06 2017
% 1.1 Callback annotation 	- KPL	14 06 2017
% 1.0 Initial revision 		- AES 	01 01 2017 

% This program walks through a uniquely named SCL5 description of a protocol
% and searches for areas to optimize the parse. A type decision parse can
% be optimized if each element of the type decision has a kind/type element
% that is constrained to be a unique value in that type decision. These
% are then optimizable as when the code is generated the kind can be parsed
% and then based on the unique value of it, the type of the type decision is
% then known and can be parsed. Otherwise each type must be attempted to be
% fully parsed until the parse succeeds, indicating the correct type was found.

% The input to the program is a SCL5 file named "protocol"_callbackAnnotated.scl5.
% The input file is a SCL5 description of a protocol that has unique naming of all
% declaration and references and has attempted to optimize callbacks by adding
% callback annotations

% The output of this program is a SCL5 file named "protocol"_UID_annotated.scl5.
% The output file is the imput SCL5 file with parse optimizations added as annotations
% in the respective rule definitions. Additionally callback optimizations will be
% removed when found in conflict with parse optimizations.


% Base grammars

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
	[opt at] [opt number] [opt number] [opt global] [opt optimizable] 
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
    [id] [opt hatID] [opt global] [opt optimizable]
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
	% Global variable to hold the [id]'s of rules that need
	% to have the @ callback annotation removed
	construct RemoveAT [repeat id]
	export RemoveAT
	% Global variable to hold the [id]'s of rules that need
	% to have a callback with the [id] [id] annotation removed
	construct RemoveID [repeat id]
	export RemoveID
	construct TPRULES [repeat type_rule_definition]
		_ [^ P]	% Extract all of the original type rule definitions from the program
	by
		P [annotateTypeRules TPRULES] 
			[checkforOptimization]
			[removeOptimizedCallbackANN]
end function


% Step 1: Annotate all the type rules and type decision rules with
% the new parser optimization annotations
rule annotateTypeRules typeRules [repeat type_rule_definition]
	replace $ [type_rule_definition]
		TRD [type_rule_definition]
	by
		TRD [annotatePOS]
			[getSizeAndValue typeRules]
			
end rule

% Step 1.1: Annotate all [element_type] in each rule definition
% with a POS tag if there is a POS constarint on the [element_type]
function annotatePOS
	replace [type_rule_definition]
		ID [id] '^ SHORT [id] '::= 'SEQUENCE OS [opt size_constraint] '{
			LE [list element_type] OC [opt ',]
		'} ENC [opt encoding_grammar_indicator] SZ [opt size_markers_block]
		'<transfer>
		RETR [repeat transfer_statement]
		'</transfer>
		CST [opt constraints_block]
	construct POSConstraints [repeat pos_expression]
		_ [^ RETR]	% Extract all the POS constraints so they can be searched
	construct NEWLE [list element_type]
		LE [checkMatchingPOSConstraint POSConstraints] [checkMatchingPOSConstraintOptional POSConstraints]
		% Annotate all the [element_type]'s with POS where required
	by
		ID '^ SHORT '::= 'SEQUENCE OS '{
			NEWLE OC
		'} ENC SZ
		'<transfer>
		RETR
		'</transfer>
		CST
end function

% Check each [element_type] in the list to see if its
% [id] matches the [id] of a POS constraint. If it does
% append a POS to the end of the [element_type] This 
% rule will not check optional [element_type]
rule checkMatchingPOSConstraint POSConstraints [repeat pos_expression]
	replace $ [element_type]
		LONG [id] '^ SHORT [id] TP [type]
	deconstruct * [pos_expression] POSConstraints
		'POS '( LONG ')
	by
		LONG '^ SHORT TP 'POS
end rule

% Check each [element_type] in the list to see if its
% [id] matches the [id] of a POS constarint. If it does
% append a POS the the end of the [element_type] This
% rule will only check optional [element_type]
rule checkMatchingPOSConstraintOptional POSConstraints [repeat pos_expression]
	replace $ [element_type]
		LONG [id] '^ SHORT [id] TP [type] 'OPTIONAL
	deconstruct * [pos_expression] POSConstraints
		'POS '( LONG ')
	by
		LONG '^ SHORT TP 'OPTIONAL 'POS
end rule


% Step 1.2: Iterate through each sequence rule definition
% and annotate its definition with the size and value
% annotation for the optimization (See note in local grammar
% for more information)
function getSizeAndValue typeRules [repeat type_rule_definition]
	replace [type_rule_definition]
		ID [id] '^ SHORT [id] '::= 'SEQUENCE OS [opt size_constraint] '{
			LE [list element_type] OC [opt ',]
		'} ENC [opt encoding_grammar_indicator] SZ [opt size_markers_block]
		'<transfer>
		RETR [repeat transfer_statement]
		'</transfer>
		CST [opt constraints_block]
	% NOTE: global constraints will be overwritten by any other optimizable element_types
	construct sizeAndValue [opt annotation]
		_ [getBuiltinType LE RETR] [getSizeBasedType typeRules LE RETR] [getGlobalConstraints LE RETR] [addGlobalAnnotation RETR]
		% Attempt to construct an annotation for the rule with every type of [element_type] with different rules for each
	by
		ID '^ SHORT sizeAndValue '::= 'SEQUENCE OS '{
			LE OC
		'} ENC SZ
		'<transfer>
		RETR
		'</transfer>
		CST
end function 

% Function to construct an annotation for any of
% the built in [element_type]'s of integer and string
function getBuiltinType LE [list element_type] RETR [repeat transfer_statement]
	replace [opt annotation]
		A [opt annotation]
	by 
		A [getIntegerType LE RETR] [getStringType LE RETR]
		% Attempt to build an annotation for an integer and string type
end function

% Function to create an annotation for a list of
% [element_type] where that list has an integer entry with
% defined size and has a value constraint on its value
function getIntegerType ListElements [list element_type] Transfers [repeat transfer_statement]
	replace [opt annotation]
		A [opt annotation]
	% Looking for the first field in type_rule_definition
	deconstruct * [element_type] ListElements
		REF [decl] 'INTEGER '( 'SIZE NUM [number] 'BYTES ') OP [opt endian]
	deconstruct REF
		LONG [id] '^ SHORT [id]
	% Discovered [id] (LONG) must have a value constraint
	deconstruct * [transfer_statement] Transfers
		'Back '{ LONG '== VALUE [number] '}
	by
		'@ NUM VALUE 	% Annotation is the size and constrained value
end function

% Function to create an annotation for a list of
% [element_type] where that list has an octet string entry 
% with defined size and has a value constraint on its value
function getStringType ListElements [list element_type] Transfers [repeat transfer_statement]
	replace [opt annotation]
		A [opt annotation]
	% Looking for the first field in type_rule_definition
	deconstruct * [element_type] ListElements
		REF [decl] 'OCTET 'STRING '( 'SIZE NUM [number] 'BYTES ') OPEN [opt endian] OPSL [opt slack] %', REST [list element_type]
	deconstruct REF
		LONG [id] '^ SHORT [id]
	% Discovered [id] (LONG) must have a value constraint
	deconstruct * [transfer_statement] Transfers
		'Back '{ LONG '== VALUE [number] '}
	by
		'@ NUM VALUE 	% Annotation is the size and constrained value
end function

% Function to construct an annotation for a sized based
% [element_type] where the type is user defined and must
% be discovered by examining its definition
function getSizeBasedType typeRules [repeat type_rule_definition] LE [list element_type] RETR [repeat transfer_statement]
	replace [opt annotation]
		A [opt annotation]
	deconstruct * [element_type] LE
		REF [decl] TYPE [id] '( 'SIZE 'DEFINED') OPEN [opt endian] OPSL [opt slack]
	deconstruct REF
		LONG [id] '^ SHORTID [id]
	% Must have a value constraint on the [id] before we try and find its size
	deconstruct * [transfer_statement] RETR
		'Back '{ LONG REP [repeat dot_rp] '== VALUE [number] '}
	construct finalSize [number]
		_ [findRecursiveSize typeRules TYPE REP]	% Find the size of the type by searching
													% for the type's definition
	by 
		'@ finalSize VALUE 	% Annotation is the size and constrained value
end function

% This will recursively look for the last field that is in the constraint and find its size
% It will also ensure that it is looking for the correct field inside of a [type_rule_definition]
% and not just the first one
function findRecursiveSize typeRules [repeat type_rule_definition] TYPE [id] REP [repeat dot_rp]
	replace [number] 
		N [number]
	deconstruct * [type_rule_definition] typeRules
		TYPE '^ SHORT [id] ANN [opt annotation] '::= 'SEQUENCE OS [opt size_constraint] '{
			LE [list element_type] OC [opt ',]
		'} ADD [opt scl_additions]
	deconstruct REP
		'. RE [id] REST [repeat dot_rp]
	deconstruct * [element_type] LE
		RE '^ SHORTID2 [id] NEWTYPE [type]
	construct currentElement [element_type]
		RE '^ SHORTID2 NEWTYPE
	% Find the final element of the list that matches
	construct finalElementType [element_type]
		currentElement [findRecursiveSizeHelper typeRules LE REP]
	by
		% Once the final element is discovered, its size can be evaluated
		N [getIntegerSize finalElementType] [getStringSize finalElementType]
end function

% Recursive function to find the final element in the 
% [type_rule_definition] of the type that is being evaluated
function findRecursiveSizeHelper typeRules [repeat type_rule_definition] LE [list element_type] REP [repeat dot_rp] 
	replace [element_type]
		ET [element_type]
	deconstruct REP
		'. RE [id] REST [repeat dot_rp]
	deconstruct * [element_type] LE
		RE '^ SHORT [id] TYPE [id] '( 'SIZE 'DEFINED') OPEN [opt endian] OPSL [opt slack]
	deconstruct * [type_rule_definition] typeRules
		TYPE '^ SHORTID [id] ANN [opt annotation] '::= 'SEQUENCE OS [opt size_constraint] '{
			NEWLE [list element_type] OC [opt ',]
		'} ADD [opt scl_additions]
	construct element [element_type]
		ET [findRecursiveSizeHelper typeRules NEWLE REST]
	deconstruct REST
		'. finalRE [id]
	deconstruct * [element_type] NEWLE
		finalRE '^ SHORTID2 [id] NEWTYPE [builtin_type]
	by
		finalRE '^ SHORTID2 NEWTYPE
end function

% If the discovered final element is an integer type
% then the size is taken from the [element_type] description
function getIntegerSize ListElement [element_type]
	replace [number]
		N [number]
	% Looking for the specified field in type_rule_definition
	deconstruct ListElement
		LONG [id] '^ SHORT [id] 'INTEGER '( 'SIZE NUM [number] 'BYTES ') OP [opt endian]
	by
		NUM
end function

% If the discovered final element is an octet string
% type then the size is taken from the [element_type] description
function getStringSize ListElement [element_type]
	replace [number]
		N [number]
	% Looking for the specified field in type_rule_definition
	deconstruct ListElement
		LONG [id] '^ SHORT [id] OCTET 'STRING '( 'SIZE NUM [number] 'BYTES ') OPEN [opt endian] OPSL [opt slack] %', REST [list element_type]
	by
		NUM
end function

% GLOBAL are constraints that have been placed on fields in
% other modules. They are declared as external variables in 
% this current module

% Function to create an annotation with a global
% value from the global constraint if and only 
% if it has no previous value annotation
function getGlobalConstraints LE [list element_type] RETR [repeat transfer_statement]
	% Value must have a global constraint
	deconstruct * [transfer_statement] RETR
		'Back '{ 'GLOBAL '( RE [referenced_element] ') '== NUM [number] '}
	replace [opt annotation]
		A [opt annotation]
	% If already annotated by previous rules then quit; Previous value is valid
	deconstruct not A
		'@ SZ [opt number] VAL [opt number] OPOP [opt optimizable]
	by
		'@ '0 NUM 	% Has no size since global; Constrained value is still present
end function

% If a value annotation was already generated from the
% [element_type] before exaiming the global constraints
% then the global annotation must be added to the rest
function addGlobalAnnotation RETR [repeat transfer_statement]
	replace [opt annotation]
		A [opt annotation]
	% Must have a global value constraint
	deconstruct * [transfer_statement] RETR
		'Back '{ 'GLOBAL '( RE [referenced_element] ') '== NUM [number] '}
	construct checkAnn [opt annotation]
		A [addToOptimizableAnn] [addToBlankAnn]	% Add the global tag properly
												% depending on what annotation
												% already exists
	by
		checkAnn
end function

% Add the global optimization annotation information
% to an annotation that already has the size and value
% information
function addToOptimizableAnn
	replace [opt annotation]
		ANN [opt annotation]
	% Annotation with size and value information
	deconstruct ANN
		'@ size [opt number] value [opt number] OPOP [opt optimizable]
	by
		'@ size value '@ 'GLOBAL OPOP 	% Add the @ GLOBAL tag to the value
										% to indicate it is globally constrained
end function

% Add the global optimization information to an annotation
% that is blank (no size or value information)
function addToBlankAnn
	replace [opt annotation]
		ANN [opt annotation]
	deconstruct not ANN
		'@ size [opt number] value [opt number]
	deconstruct not ANN 
		'@ size [opt number] value [opt number] '@ 'GLOBAL
	by
		'@ 'GLOBAL 	% Add @ GLOBAL tag to indicate it is globally constrained
end function


% Step 2: Examine the annotations placed on the [type_rule_definition]'s to 
% determine if any [type_decision] rules are optimizable. Annotations will
% be added to the [type_decision] rules themselves and then inspected to see
% if the conditions for optimization hold. If they do then @ optimizable
% tags will be added to the [type_decision] rules
function checkforOptimization
	replace [program]
		P [program]
	% IMPORTANT: Need to extract type_rule_definitions again, because they are 
	% now annotated, cannot pass the originally extracted type_rule_definitions 
	% from main function.
	construct TPRULES [repeat type_rule_definition]
		_ [^ P]
	by
		P [annotateTypeDecisionsHelper TPRULES]
			[checkOptimizable TPRULES]
			[fillTypeRefs]
			[checkGlobalOptimization]
			[ensureGlobalSizeValues TPRULES]

end function

% Step 2.1: Any type decision rules must have their [type_decision]
% portion annotated. Each [type_reference] in the [type_decision]
% is annotated with a copy of the annotation that is placed on its
% rule definition, which is found through a copy of all the newly 
% annotated type rules
rule annotateTypeDecisionsHelper typeRules [repeat type_rule_definition]
	replace $ [construction_assignment_statement]
		LONG [id] '^ SHORT [id] '::= '( TR [type_reference] RTR [repeat alternative_decision] ') OP [opt scl_additions]
	by
		% Add a copy of the annotation to the first [type_reference] and set of [alternative_decision]
		LONG '^ SHORT '::= '( TR [copyAnnotation typeRules] RTR [copyAnnotationAltDecision typeRules] ') OP
end rule

% NOTE: not dealing with opt dotID type_reference (imported type references)

% Function to find the annotation for a [type_reference] in
% a type decision from its [type_rule_definition] and copy it
% to the [type_reference]
function copyAnnotation typeRules [repeat type_rule_definition]
	replace [type_reference]
		TR [type_reference]
	deconstruct TR
		ID [id] OP [opt dotID]
	% Find the definition of the rule with [id] matching that of the [type_reference]
	deconstruct * [type_rule_definition] typeRules
		ID '^ SHORT [id] ANN [opt annotation] '::= 'SEQUENCE OS [opt size_constraint] '{
			LE [list element_type] OC [opt ',]
		'} ENC [opt encoding_grammar_indicator] SZ [opt size_markers_block]
		'<transfer>
		RETR [repeat transfer_statement]
		'</transfer>
		CST [opt constraints_block]
	by
		ID OP ANN 	% Copy the annotation to the type reference
end function

% Function to extract each [type_reference] from a set of
% [alternative_decision] and send it to the annotation find
% and copy rule
rule copyAnnotationAltDecision typeRules [repeat type_rule_definition]
	replace $ [alternative_decision]
		'| TR [type_reference]
	by
		'| TR [copyAnnotation typeRules]
end rule

% Step 2.2: Checks if Type decisions are optimizable;
% Need to check if all of the sizes of the fields are the SAME and all values are mutually exclusive!
% If these conditions are not satisfied, remove the type_reference that breaks the conditions.
% The original construction_assignment_statement is matched against the new one. If they are equal and 
% nothing was removed, then the construction_assignment_statement is optimizable. 
rule checkOptimizable typeRules [repeat type_rule_definition]
	replace $ [construction_assignment_statement]
		LONG [id] '^ SHORT [id] '::= '( TR [type_reference] RTR [repeat alternative_decision]') OPT [opt scl_additions]	
	% Ensure that TR has an annotation
	deconstruct TR
		ID [id] OPTID [opt dotID] '@ SZ [opt number] VL [opt number] OPGLOB [opt global]
	where
		RTR [allHaveAnnotations]	% Ensure that all the references in the 
									% [alternative_decision] set have annotations
	% Create a copy of the rule and remove any [type_reference]'s where the size
	% in the annotation does not match or the value is not unique
	construct checkedAssignment [construction_assignment_statement]
		LONG '^ SHORT '::= '( TR RTR [removeDuplicates TR] ')
	where
		checkedAssignment [isIdenticalToOriginal LONG SHORT TR RTR]	% Compare the new [construction_assignment_statement]
																	% to the original which is passed in as parameters
	by
		% The new statement is the same as the original which means that it is optimizable
		% Annotate the rule itself with the @ optimizable tag and then annotate each [type_reference]
		% in the decision with @ optimizable tags as well
		LONG '^ SHORT OPGLOB '@ 'optimizable '::= '( TR [annotateOptimizableRef] RTR [annotateRepeatOptimizableRef] ') OPT
end rule

% Match everly element of a set of [alternative_decision] to
% a pattern that contains annotations
rule allHaveAnnotations
	match $ [alternative_decision]
		'| ID [id] OPTID [opt dotID] '@ SZ [opt number] VL [opt number] OPGLOB [opt global]
end rule

% Function to remove any elements from the [repeat alternative_decision]
% where the annotation conditions do not hold. To hold, the annotation must
% match the size from the passed in reference's annotation and must have 
% a different value from any of the already examined references (including parameter)
rule removeDuplicates TypeReference [type_reference]
	replace [repeat alternative_decision]
		'| TR [type_reference] REST [repeat alternative_decision]
	deconstruct TR
		ID [id] DTID [opt dotID] '@ SZ [opt number] VL [opt number] OPGLOB [opt global]
	deconstruct TypeReference
		TRID [id] TRDTID [opt dotID] ANN [opt annotation]
	where
		ANN [differentSize SZ] [equalValue VL]	% Check the inverse of the annotation conditions
												% if either of the inverse conditions pass then
												% the rule will proceed and remove the [alternative_decision]
	by
		REST [removeDuplicates TR]	% Remove the current element as it failed the conditions and
									% proceed examining the rest of the elements
end rule

% Condition function that will fail if the annotation
% under examination has a size [number] that
% matches the one in the parameter
function differentSize Size [opt number]
	match [opt annotation]
		'@ SZ [opt number] VL [opt number]
	where not
		SZ [= Size]
end function

% Condition function that will fail if the annotation
% under examination has a value that is not equal to
% the one in the parameter
function equalValue Value [opt number]
	match [opt annotation]
		'@ SZ [opt number] VL [opt number]
	where
		VL [= Value]
end function

% Condition function that will attempt to match the
% [construction_assignment_statement] under test
% to a deconstructed [construction_assignment_statement]
% that is passed in through parameters
function isIdenticalToOriginal Long [id] Short [id] TR [type_reference] RTR [repeat alternative_decision]
	match [construction_assignment_statement]
		CAS [construction_assignment_statement]
	deconstruct CAS
		Long '^ Short '::= '( TR RTR ') OP [opt scl_additions]
end function

% Annotate a [type_reference] in a [type_decision] that is
% optimizable with the @ optimizable tag in addition to its
% current annotation
function annotateOptimizableRef
	replace [type_reference]
		ID [id] DTID [opt dotID] '@ SZ [opt number] VL [opt number] OPGLOB [opt global] OPT [opt optimizable]
	by
		ID DTID '@ SZ VL OPGLOB '@ 'optimizable
end function

% Iterate through a set of [alternative_decision] and 
% send the extracted [type_reference]'s to the rule to
% have their annotations updated
rule annotateRepeatOptimizableRef
	replace $ [repeat alternative_decision]
		'| TR [type_reference] REST [repeat alternative_decision]
	by
		'| TR [annotateOptimizableRef] REST
end rule

% Step 2.3: For each type decision rule that is marked with an 
% @ optimizable, mark the [type_rule_definition] of each type in
% the [type_decision] with @ optimizable as well
function fillTypeRefs
	replace [program]
		P [program]
	% Extract a new copy of all the [construction_assignment_statement]'s
	% as they have been annotated now
	construct TPDECS [repeat construction_assignment_statement]
		_ [^ P]
	% Global variable to hold all the [type_reference]'s from optimizable [type_decision]'s
	construct fillRefs [repeat type_reference]
	export fillRefs
	construct checkForRefs [repeat construction_assignment_statement]
		TPDECS [checkForMatch]	% Populate the global variable fillRefs
	by
		P [annotateTypeRulesOpt]	% Annotate the [type_rule_definition] with @ optimizable
end function

% Check if a [construction_assignment_statement] is marked with an
% @ optimizable and if it is, save a copy of all its [type_reference]'s 
% in the [type_decision] to the global variable fillRefs
rule checkForMatch
	replace $ [construction_assignment_statement]
		LONG [id] '^ SHORT [id] OPGLOB [opt global] '@ 'optimizable '::= '( TR [type_reference] RTR [repeat alternative_decision] ') OPT [opt scl_additions]
	import fillRefs [repeat type_reference]
	construct typeRefs [repeat type_reference]
		_ [^ RTR]	% Extract the [type_reference]'s from the [alternative_decision]
	export fillRefs
		fillRefs [. TR] [. typeRefs]	% Save the contents of the [type_decision]
	by
		LONG '^ SHORT OPGLOB '@ 'optimizable '::= '( TR RTR ') OPT 	% No replacement
end rule

% Step 2.3.1: Annotate each [type_rule_definition] that has a 
% [type_reference] saved in the global fillRefs with an
% @ optimizable tag in addition to the annotations it already has
rule annotateTypeRulesOpt
	replace $ [type_rule_definition]
		LONG [id] '^ SHORT [id] ANN [opt annotation] '::= 'SEQUENCE OS [opt size_constraint] '{
			LE [list element_type] OC [opt ',]
		'} ADD [opt scl_additions]
	import fillRefs [repeat type_reference]
	% Only mark the definitions that have an [id] in the global as they are optimizable
	deconstruct * [type_reference] fillRefs
		LONG dotID [opt dotID] OPTANN [opt annotation]
	deconstruct ANN
		'@ size [opt number] value [opt number] OPGLOB [opt global]
	% Generate a new annotation with all the old information plus the @ optimizable
	construct finalANN [opt annotation]
		'@ size value OPGLOB '@ 'optimizable
	by 
		LONG '^ SHORT finalANN'::= 'SEQUENCE OS '{
			LE OC
		'} ADD	
end rule


% Step 2.4: Ensure there is a global constraint to generate 
% optimized global type decisions
rule checkGlobalOptimization
	replace $ [construction_assignment_statement]
		LONG [id] '^ SHORT [id] '@ 'GLOBAL '@ 'optimizable '::= '( TR [type_reference] RTR [repeat alternative_decision] ') OP [opt scl_additions]
	deconstruct not * [transfer_statement] OP
		'Back '{ 'GLOBAL '( RE [referenced_element] ') '}
	% If there is not a global constraint then emit the error messgae
	construct errmsg [stringlit]
		_ [+ "WARNING: Type decision is globally optimizable without reference to global variable constraint in transfer block! "]
		[+ "Check "] [+ LONG] [+ " type decision and add GLOBAL constraint."]
		[print]
	by
		LONG '^ SHORT '@ 'optimizable '::= '( TR RTR ') OP 	% No replacement
end rule

% Step 2.5:
rule ensureGlobalSizeValues TPRULES [repeat type_rule_definition]
	replace $ [construction_assignment_statement]
		LONG [id] '^ SHORT [id] '@ 'GLOBAL '@ 'optimizable '::= '( TR [type_reference] RTR [repeat alternative_decision] ') OP [opt scl_additions]
	construct newTR [type_reference]
		TR [checkTR TPRULES]
	construct newRTR [repeat alternative_decision]
		RTR [checkRTR TPRULES]
	%construct fixTypeRules
	%	[revertOptimizableTypeRules]
	by
		LONG '^ SHORT '@ 'GLOBAL '@ 'optimizable '::= '( newTR newRTR ') OP  %'@ 'optimizable
end rule

function checkTR TPRULES [repeat type_rule_definition]
	replace [type_reference]
		ID [id] OPID [opt dotID] OPANN [opt annotation]
	deconstruct * [type_rule_definition] TPRULES
		ID '^ SHORT [id] ANN [opt annotation] '::= 'SEQUENCE OS [opt size_constraint] '{
			LE [list element_type] OC [opt ',]
		'} ENC [opt encoding_grammar_indicator] SZ [opt size_markers_block]
		'<transfer>
		RETR [repeat transfer_statement]
		'</transfer>
		CST [opt constraints_block]
	construct newANN [opt annotation]
		OPANN [getGlobalConstraints LE RETR]  [addGlobalAnnotation RETR]
	by
		ID OPID newANN
end function

rule checkRTR TPRULES [repeat type_rule_definition]
	replace $ [alternative_decision]
		'| ID [id] OPID [opt dotID] OPANN [opt annotation]
	deconstruct * [type_rule_definition] TPRULES
		ID '^ SHORT [id] ANN [opt annotation] '::= 'SEQUENCE OS [opt size_constraint] '{
			LE [list element_type] OC [opt ',]
		'} ENC [opt encoding_grammar_indicator] SZ [opt size_markers_block]
		'<transfer>
		RETR [repeat transfer_statement]
		'</transfer>
		CST [opt constraints_block]
	construct newANN [opt annotation]
		OPANN [getGlobalConstraints LE RETR]  [addGlobalAnnotation RETR]
	by
		'| ID OPID newANN
end rule

% Step 3: Remove the callback optimization in rules where the better
% parse optimization (@ optimizable) is being used and revert to
% standard callback
function removeOptimizedCallbackANN
	replace [program]
		P [program]
	by
		P	[findCallbackTypeDecision]
			[removeAtANN]
			[removeIDANN]
end function

% Step 3.1: Find any type decision rules that have the [annotated_callback]
% form of '^ [id] [id] and are also @ optimizable; Remove the callback
% and populate globals with info to edit the callbacks related to this definition
rule findCallbackTypeDecision
	replace $ [construction_assignment_statement]
		LONG [id] '^ SHORT [id] '@ 'optimizable '::= '( TREF [type_reference] RTR [repeat alternative_decision] ') OP [opt scl_additions]
	deconstruct [opt scl_additions] OP
		GR [opt encoding_grammar_indicator] 
		SZ [opt size_markers_block] 
		TR [opt transfer_rules_block]
    	CB [opt constraints_block] 
    deconstruct [opt transfer_rules_block] TR
    	'<transfer>
    	TS [repeat transfer_statement]
    	'</transfer>
    % Check if the rule has the optimized callback
    deconstruct * [transfer_statement] TS
    	'Callback '^ ID1 [id] ID2 [id]
    construct NewTS [repeat transfer_statement]
    	_ [saveTS each TS]	% Rebuild the [transfer_rules_block] saving only non-callbacks
    construct NewTR [opt transfer_rules_block]
    	_ [constructTransferBlock NewTS]	% Generate a [transfer_rules_block] with the saved
    										% [transfer_statement]'s; If there are none then
    										% leave as null since it is [opt]
    construct NewOP [opt scl_additions]
    	GR
    	SZ
    	NewTR
    	CB
    import RemoveAT [repeat id]
    export RemoveAT
    	RemoveAT [. LONG]	% Mark the [id] to have an @ [id] callback_annotation removed
    deconstruct [type_reference] TREF
		TYPE [id] DOT [opt dotID] ANN [opt annotation]
	construct IDS [repeat id]
		_ [unpackRTR each RTR]	% Unpack all the [id]'s from the [alternative_decision]
    import RemoveID [repeat id]
    export RemoveID
    	RemoveID [. TYPE] [. IDS]	% Mark all the [id]'s from the [type_decision] to have
    								% their annotated callbacks removed
    % Send a warning message to tell the user of this optimization change
    construct Err [id]
	_ [+ "Warning, Callback optimization in \""] [+ LONG] [+ "\" is being replaced by Parse Optimization "]
	construct Message [id]
		_	[message Err]
	by
		LONG '^ SHORT '@ 'optimizable '::= '( TREF RTR ') NewOP
end rule

% Function to save any transfer_statement that is not a callback
function saveTS TS [transfer_statement]
	deconstruct not [transfer_statement] TS
		'Callback ANN [opt callback_annotation]
	replace [repeat transfer_statement]
		RTS [repeat transfer_statement]
	by
		RTS [. TS]
end function

% Function to remove a [callback_annotation] from the [transfer_statement]
function removeCallbackANN TS [transfer_statement]
	deconstruct [transfer_statement] TS
		'Callback ANN [opt callback_annotation]
	replace [repeat transfer_statement]
		RTS [repeat transfer_statement]
	construct callback [transfer_statement]
		'Callback
	by
		RTS [. callback]
end function

% Function to construct a [transfer_rules_block] if there is at least
% one present [transfer_statement]; If not remove the [transfer_rules_block]
function constructTransferBlock NewTS [repeat transfer_statement]
	replace [opt transfer_rules_block]
		TR [opt transfer_rules_block]
	% Only build the [transfer_rules_block] if there is at least one [transfer_statement]
	deconstruct [repeat transfer_statement] NewTS
		TS [transfer_statement] REST [repeat transfer_statement]
	construct NewTR [opt transfer_rules_block]
		'<transfer>
    	NewTS
    	'</transfer>
	by
		NewTR
end function

% Function to unpack the information from a [repeat alternative_decision]
function unpackRTR RTR [alternative_decision]
	replace [repeat id]
		IDs [repeat id]
	deconstruct [alternative_decision] RTR
		'| TYPE [id] DOT [opt dotID] ANN [opt annotation]
	by
		IDs [. TYPE]
end function

% Step 3.2: Find the rule with the '@ [id] [callback_annotation] that matches
% the [id] from RemoveAT which is marking it for removal and remove it so it
% is back to standard 'Callback form
rule removeAtANN
	replace $ [type_rule_definition]
		LONG [id] '^ SHORT [id] '::= 'SEQUENCE OS [opt size_constraint] '{
			LE [list element_type] OC [opt ',]
		'} OP [opt scl_additions]
	% Rule must have an @ [id] annotated callback to consider removal
	deconstruct * [transfer_statement] OP
		'Callback '@ TYPE [id]
	import RemoveAT [repeat id]
	% Check if rule is marked for the [callback_annotation] removal
	deconstruct * [id] RemoveAT
		TYPE
	deconstruct [opt scl_additions] OP
		GR [opt encoding_grammar_indicator] 
		SZ [opt size_markers_block] 
		TR [opt transfer_rules_block]
    	CB [opt constraints_block] 
    deconstruct [opt transfer_rules_block] TR
    	'<transfer>
    	TS [repeat transfer_statement]
    	'</transfer>
    construct NewTS [repeat transfer_statement]
    	_ [saveTS each TS] [removeCallbackANN each TS]	% Generate a new set of [transfer_statement]'s
    													% saving all the old ones and removing the
    													% [callback_annotation] from the Callback
    													% Iterate through all as we do not know the 
    													% position of the callback in the [transfer_rules_block]
    construct NewTR [opt transfer_rules_block]
    	'<transfer>
    	NewTS
    	'</transfer>
    construct NewOP [opt scl_additions]
    	GR
    	SZ
    	NewTR
    	CB
	by
		LONG '^ SHORT '::= 'SEQUENCE OS '{
			LE OC
		'} NewOP
end rule

% Step 3.3: Find the rule with the [id] [id] callback_annotation that matches
% the [id] from RemoveID which is marking it for removal and remove the entire callback
rule removeIDANN
	replace $ [type_rule_definition]
		LONG [id] '^ SHORT [id] ANN [opt annotation] '::= 'SEQUENCE OS [opt size_constraint] '{
			LE [list element_type] OC [opt ',]
		'} OP [opt scl_additions]
	% Rule must have the [id] [id] annotated callback to consider removal
	deconstruct * [transfer_statement] OP
		'Callback ID1 [id] ID2 [id]
	import RemoveID [repeat id]
	% Check if rule is marked for the callback removal
	deconstruct * [id] RemoveID
		LONG
	deconstruct [opt scl_additions] OP
		GR [opt encoding_grammar_indicator] 
		SZ [opt size_markers_block] 
		TR [opt transfer_rules_block]
    	CB [opt constraints_block] 
    deconstruct [opt transfer_rules_block] TR
    	'<transfer>
    	TS [repeat transfer_statement]
    	'</transfer>
    construct NewTS [repeat transfer_statement]
    	_ [saveTS each TS]	% Rebuild the [transfer_rules_block] saving only non-callbacks
    construct NewTR [opt transfer_rules_block]
    	'<transfer>
    	NewTS
    	'</transfer>
    construct NewOP [opt scl_additions]
    	GR
    	SZ
    	NewTR
    	CB
	by
		LONG '^ SHORT ANN '::= 'SEQUENCE OS '{
			LE OC
		'} NewOP
end rule