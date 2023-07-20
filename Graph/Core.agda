module Graph.Core {L : Set} where

  data Graph : Set where
    ε   : Graph
    v_  : L → Graph
    _+_ : Graph → Graph → Graph
    _*_ : Graph → Graph → Graph
  
  infixl 6  _+_
  infixl 7  _*_
