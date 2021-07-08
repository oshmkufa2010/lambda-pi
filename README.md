# lambda-pi

This project is an educational implementation of dependent types inspired by https://www.andres-loeh.de/LambdaPi/LambdaPi.pdf.

Comparing with implementation in above paper, this project has following features:

1. All functions are total, which means that there was no runtime crash or dead loop.

2. Using substitution instead of Haskell function makes reduction steps more clearly.

3. Not using de Bruijn index makes terms easy to understand.

4. Monadic style.

Todo:

- [ ] A parser
- [ ] Dependent vector
- [ ] Sigma types
- [ ] Custom inductive types (I don't know how hard to achieve this goal...)
