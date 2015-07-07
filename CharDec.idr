
module CharDec

import DecHelper

%default total

isSpaceT : Char -> Type
isSpaceT c = isSpace c = True


isSpaceDec : (c : Char) -> Dec (isSpaceT c)
isSpaceDec c with (isSpace c) 
  | True  = Yes Refl
  | False = No falseNotTrue 



isUpperT : Char -> Type
isUpperT c = isUpper c = True

isUpperDec : (c : Char) -> Dec (isUpperT c)
isUpperDec c with (isUpper c)
  | True  = Yes Refl
  | False = No falseNotTrue



isLowerT : Char -> Type
isLowerT c = isLower c = True

isLowerDec : (c : Char) -> Dec (isLowerT c)
isLowerDec c with (isLower c)
  | True  = Yes Refl
  | False = No falseNotTrue


isAlphaT : Char -> Type
isAlphaT c = isAlpha c = True

isAlphaDec : (c : Char) -> Dec (isAlphaT c)
isAlphaDec c with (isAlpha c)
  | True  = Yes Refl
  | False = No falseNotTrue
-- TODO extract the commonalities?  will it make it shorter even?



isDigitT : Char -> Type
isDigitT c = isDigit c = True

isDigitDec : (c : Char) -> Dec (isDigitT c)
isDigitDec c with (isDigit c)
  | True  = Yes Refl
  | False = No falseNotTrue


isAlphaNumT : Char -> Type
isAlphaNumT c = isAlphaNum c = True

isAlphaNumDec : (c : Char) -> Dec (isAlphaNumT c)
isAlphaNumDec c with (isAlphaNum c)
  | True  = Yes Refl
  | False = No falseNotTrue




isNLT : Char -> Type
isNLT c = isNL c = True

isNLDec : (c : Char) -> Dec (isNLT c)
isNLDec c with (isNL c)
  | True  = Yes Refl
  | False = No falseNotTrue


isHexDigitT : Char -> Type
isHexDigitT c = isHexDigit c = True

isHexDigitDec : (c : Char) -> Dec (isHexDigitT c)
isHexDigitDec c with (isHexDigit c)
  | True  = Yes Refl
  | False = No falseNotTrue



isOctDigitT : Char -> Type
isOctDigitT c = isOctDigit c = True

isOctDigitDec : (c : Char) -> Dec (isOctDigitT c)
isOctDigitDec c with (isOctDigit c)
  | True  = Yes Refl
  | False = No falseNotTrue
