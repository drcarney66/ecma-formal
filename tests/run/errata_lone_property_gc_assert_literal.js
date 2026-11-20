// expect: stop: erratum LonePropertyGeneralCategoryAssert sec-runtime-semantics-unicodematchpropertyvalue-p-v#0 2
// args: --erratum LonePropertyGeneralCategoryAssert=literal
// CompileToCharSet's lone \p{X} (Erratum LonePropertyGeneralCategoryAssert): the
// literal reading passes the String "General_Category" to UnicodeMatchPropertyValue
// and asks it for a binary property's name, and the run stops as the erratum.
/\p{ASCII}/u.test("a");
