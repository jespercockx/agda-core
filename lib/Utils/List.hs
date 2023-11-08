module Utils.List where

data All b = ANil
           | ACons b (All b)

