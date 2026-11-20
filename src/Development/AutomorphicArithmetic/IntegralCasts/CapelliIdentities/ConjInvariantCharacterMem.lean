import Mathlib

noncomputable def UpperTheory.Reformulated.B.Yzd4.cT :
    {A : Type} →
      [inst : CommRing A] →
        @RingHom A A (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
            (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))) →
          {m p : Type} → Matrix m p A → Matrix p m A := sorry
















private theorem cT_mul {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
    (σ : A →+* A) (a b : Matrix n n A) :
    UpperTheory.Reformulated.B.Yzd4.cT σ (a * b) = UpperTheory.Reformulated.B.Yzd4.cT σ b * UpperTheory.Reformulated.B.Yzd4.cT σ a := by sorry



private theorem cT_one {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
    (σ : A →+* A) : UpperTheory.Reformulated.B.Yzd4.cT σ (1 : Matrix n n A) = 1 := by sorry



theorem UpperTheory.Reformulated.B.Yzd4.aux2 :
    ∀ {A : Type} [inst : CommRing A] {n : Type} [inst_1 : Fintype n] [inst_2 : DecidableEq n]
      (σ :
        @RingHom A A (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
          (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))
      (J : Matrix n n A)
      {a b : @Matrix.GeneralLinearGroup n A inst_2 inst_1 (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))},
      @Membership.mem
          (@Matrix.GeneralLinearGroup n A inst_2 inst_1 (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
          (Set
            (@Matrix.GeneralLinearGroup n A inst_2 inst_1 (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))
          (@Set.instMembership
            (@Matrix.GeneralLinearGroup n A inst_2 inst_1 (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))
          (@Set.ofPred
            (@Matrix.GeneralLinearGroup n A inst_2 inst_1 (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
            fun
              (g :
                @Matrix.GeneralLinearGroup n A inst_2 inst_1
                  (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))) ↦
            @Eq (Matrix n n A)
              (@HMul.hMul (Matrix n n A) (Matrix n n A) (Matrix n n A)
                (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid n n n A inst_1
                  (@Distrib.toMul A
                    (@instDistribOfSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))
                  (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))
                (@HMul.hMul (Matrix n n A) (Matrix n n A) (Matrix n n A)
                  (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid n n n A inst_1
                    (@Distrib.toMul A
                      (@instDistribOfSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))
                    (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))
                  (@UpperTheory.Reformulated.B.Yzd4.cT A inst σ n n
                    (@Units.val (Matrix n n A)
                      (@Semiring.toMonoid (Matrix n n A)
                        (@Matrix.semiring n A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)) inst_1 inst_2))
                      g))
                  J)
                (@Units.val (Matrix n n A)
                  (@Semiring.toMonoid (Matrix n n A)
                    (@Matrix.semiring n A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)) inst_1 inst_2))
                  g))
              J)
          a →
        @Membership.mem
            (@Matrix.GeneralLinearGroup n A inst_2 inst_1 (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
            (Set
              (@Matrix.GeneralLinearGroup n A inst_2 inst_1 (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))
            (@Set.instMembership
              (@Matrix.GeneralLinearGroup n A inst_2 inst_1 (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))
            (@Set.ofPred
              (@Matrix.GeneralLinearGroup n A inst_2 inst_1 (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
              fun
                (g :
                  @Matrix.GeneralLinearGroup n A inst_2 inst_1
                    (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))) ↦
              @Eq (Matrix n n A)
                (@HMul.hMul (Matrix n n A) (Matrix n n A) (Matrix n n A)
                  (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid n n n A inst_1
                    (@Distrib.toMul A
                      (@instDistribOfSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))
                    (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))
                  (@HMul.hMul (Matrix n n A) (Matrix n n A) (Matrix n n A)
                    (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid n n n A inst_1
                      (@Distrib.toMul A
                        (@instDistribOfSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))
                      (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))
                    (@UpperTheory.Reformulated.B.Yzd4.cT A inst σ n n
                      (@Units.val (Matrix n n A)
                        (@Semiring.toMonoid (Matrix n n A)
                          (@Matrix.semiring n A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)) inst_1
                            inst_2))
                        g))
                    J)
                  (@Units.val (Matrix n n A)
                    (@Semiring.toMonoid (Matrix n n A)
                      (@Matrix.semiring n A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)) inst_1 inst_2))
                    g))
                J)
            b →
          @Membership.mem
            (@Matrix.GeneralLinearGroup n A inst_2 inst_1 (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
            (Set
              (@Matrix.GeneralLinearGroup n A inst_2 inst_1 (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))
            (@Set.instMembership
              (@Matrix.GeneralLinearGroup n A inst_2 inst_1 (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))
            (@Set.ofPred
              (@Matrix.GeneralLinearGroup n A inst_2 inst_1 (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
              fun
                (g :
                  @Matrix.GeneralLinearGroup n A inst_2 inst_1
                    (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))) ↦
              @Eq (Matrix n n A)
                (@HMul.hMul (Matrix n n A) (Matrix n n A) (Matrix n n A)
                  (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid n n n A inst_1
                    (@Distrib.toMul A
                      (@instDistribOfSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))
                    (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))
                  (@HMul.hMul (Matrix n n A) (Matrix n n A) (Matrix n n A)
                    (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid n n n A inst_1
                      (@Distrib.toMul A
                        (@instDistribOfSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))
                      (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))
                    (@UpperTheory.Reformulated.B.Yzd4.cT A inst σ n n
                      (@Units.val (Matrix n n A)
                        (@Semiring.toMonoid (Matrix n n A)
                          (@Matrix.semiring n A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)) inst_1
                            inst_2))
                        g))
                    J)
                  (@Units.val (Matrix n n A)
                    (@Semiring.toMonoid (Matrix n n A)
                      (@Matrix.semiring n A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)) inst_1 inst_2))
                    g))
                J)
            (@HMul.hMul
              (@Matrix.GeneralLinearGroup n A inst_2 inst_1 (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
              (@Matrix.GeneralLinearGroup n A inst_2 inst_1 (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
              (@Matrix.GeneralLinearGroup n A inst_2 inst_1 (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
              (@instHMul
                (@Matrix.GeneralLinearGroup n A inst_2 inst_1
                  (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
                (@MulOne.toMul
                  (@Matrix.GeneralLinearGroup n A inst_2 inst_1
                    (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
                  (@MulOneClass.toMulOne
                    (@Matrix.GeneralLinearGroup n A inst_2 inst_1
                      (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
                    (@Monoid.toMulOneClass
                      (@Matrix.GeneralLinearGroup n A inst_2 inst_1
                        (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
                      (@DivInvMonoid.toMonoid
                        (@Matrix.GeneralLinearGroup n A inst_2 inst_1
                          (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
                        (@Group.toDivInvMonoid
                          (@Matrix.GeneralLinearGroup n A inst_2 inst_1
                            (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
                          (@Units.instGroup (Matrix n n A)
                            (@Semiring.toMonoid (Matrix n n A)
                              (@Matrix.semiring n A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)) inst_1
                                inst_2)))))))))
              a b) := by sorry











theorem UpperTheory.Reformulated.B.Yzd4.aux3 :
    ∀ {A : Type} [inst : CommRing A] {n : Type} [inst_1 : Fintype n] [inst_2 : DecidableEq n]
      (σ :
        @RingHom A A (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
          (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))
      (J : Matrix n n A),
      @Eq (Matrix n n A)
        (@HMul.hMul (Matrix n n A) (Matrix n n A) (Matrix n n A)
          (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid n n n A inst_1
            (@Distrib.toMul A (@instDistribOfSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))
            (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))
          (@HMul.hMul (Matrix n n A) (Matrix n n A) (Matrix n n A)
            (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid n n n A inst_1
              (@Distrib.toMul A (@instDistribOfSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))
              (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))
            (@UpperTheory.Reformulated.B.Yzd4.cT A inst σ n n
              (@Units.val (Matrix n n A)
                (@Semiring.toMonoid (Matrix n n A)
                  (@Matrix.semiring n A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)) inst_1 inst_2))
                (@OfNat.ofNat
                  (@Matrix.GeneralLinearGroup n A inst_2 inst_1
                    (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
                  (nat_lit 1)
                  (@One.toOfNat1
                    (@Matrix.GeneralLinearGroup n A inst_2 inst_1
                      (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
                    (@MulOne.toOne
                      (@Matrix.GeneralLinearGroup n A inst_2 inst_1
                        (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
                      (@MulOneClass.toMulOne
                        (@Matrix.GeneralLinearGroup n A inst_2 inst_1
                          (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
                        (@Monoid.toMulOneClass
                          (@Matrix.GeneralLinearGroup n A inst_2 inst_1
                            (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
                          (@DivInvMonoid.toMonoid
                            (@Matrix.GeneralLinearGroup n A inst_2 inst_1
                              (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
                            (@Group.toDivInvMonoid
                              (@Matrix.GeneralLinearGroup n A inst_2 inst_1
                                (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
                              (@Units.instGroup (Matrix n n A)
                                (@Semiring.toMonoid (Matrix n n A)
                                  (@Matrix.semiring n A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))
                                    inst_1 inst_2))))))))))))
            J)
          (@Units.val (Matrix n n A)
            (@Semiring.toMonoid (Matrix n n A)
              (@Matrix.semiring n A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)) inst_1 inst_2))
            (@OfNat.ofNat
              (@Matrix.GeneralLinearGroup n A inst_2 inst_1 (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
              (nat_lit 1)
              (@One.toOfNat1
                (@Matrix.GeneralLinearGroup n A inst_2 inst_1
                  (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
                (@MulOne.toOne
                  (@Matrix.GeneralLinearGroup n A inst_2 inst_1
                    (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
                  (@MulOneClass.toMulOne
                    (@Matrix.GeneralLinearGroup n A inst_2 inst_1
                      (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
                    (@Monoid.toMulOneClass
                      (@Matrix.GeneralLinearGroup n A inst_2 inst_1
                        (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
                      (@DivInvMonoid.toMonoid
                        (@Matrix.GeneralLinearGroup n A inst_2 inst_1
                          (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
                        (@Group.toDivInvMonoid
                          (@Matrix.GeneralLinearGroup n A inst_2 inst_1
                            (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
                          (@Units.instGroup (Matrix n n A)
                            (@Semiring.toMonoid (Matrix n n A)
                              (@Matrix.semiring n A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)) inst_1
                                inst_2))))))))))))
        J := by sorry



theorem UpperTheory.Reformulated.B.Yzd4.aux4 :
    ∀ {A : Type} [inst : CommRing A] {n : Type} [inst_1 : Fintype n] [inst_2 : DecidableEq n]
      (σ :
        @RingHom A A (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
          (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))
      (J : Matrix n n A)
      {g : @Matrix.GeneralLinearGroup n A inst_2 inst_1 (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))},
      @Membership.mem
          (@Matrix.GeneralLinearGroup n A inst_2 inst_1 (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
          (Set
            (@Matrix.GeneralLinearGroup n A inst_2 inst_1 (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))
          (@Set.instMembership
            (@Matrix.GeneralLinearGroup n A inst_2 inst_1 (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))
          (@Set.ofPred
            (@Matrix.GeneralLinearGroup n A inst_2 inst_1 (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
            fun
              (g :
                @Matrix.GeneralLinearGroup n A inst_2 inst_1
                  (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))) ↦
            @Eq (Matrix n n A)
              (@HMul.hMul (Matrix n n A) (Matrix n n A) (Matrix n n A)
                (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid n n n A inst_1
                  (@Distrib.toMul A
                    (@instDistribOfSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))
                  (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))
                (@HMul.hMul (Matrix n n A) (Matrix n n A) (Matrix n n A)
                  (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid n n n A inst_1
                    (@Distrib.toMul A
                      (@instDistribOfSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))
                    (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))
                  (@UpperTheory.Reformulated.B.Yzd4.cT A inst σ n n
                    (@Units.val (Matrix n n A)
                      (@Semiring.toMonoid (Matrix n n A)
                        (@Matrix.semiring n A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)) inst_1 inst_2))
                      g))
                  J)
                (@Units.val (Matrix n n A)
                  (@Semiring.toMonoid (Matrix n n A)
                    (@Matrix.semiring n A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)) inst_1 inst_2))
                  g))
              J)
          g →
        @Membership.mem
          (@Matrix.GeneralLinearGroup n A inst_2 inst_1 (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
          (Set
            (@Matrix.GeneralLinearGroup n A inst_2 inst_1 (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))
          (@Set.instMembership
            (@Matrix.GeneralLinearGroup n A inst_2 inst_1 (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))
          (@Set.ofPred
            (@Matrix.GeneralLinearGroup n A inst_2 inst_1 (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
            fun
              (g :
                @Matrix.GeneralLinearGroup n A inst_2 inst_1
                  (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))) ↦
            @Eq (Matrix n n A)
              (@HMul.hMul (Matrix n n A) (Matrix n n A) (Matrix n n A)
                (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid n n n A inst_1
                  (@Distrib.toMul A
                    (@instDistribOfSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))
                  (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))
                (@HMul.hMul (Matrix n n A) (Matrix n n A) (Matrix n n A)
                  (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid n n n A inst_1
                    (@Distrib.toMul A
                      (@instDistribOfSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))
                    (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))
                  (@UpperTheory.Reformulated.B.Yzd4.cT A inst σ n n
                    (@Units.val (Matrix n n A)
                      (@Semiring.toMonoid (Matrix n n A)
                        (@Matrix.semiring n A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)) inst_1 inst_2))
                      g))
                  J)
                (@Units.val (Matrix n n A)
                  (@Semiring.toMonoid (Matrix n n A)
                    (@Matrix.semiring n A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)) inst_1 inst_2))
                  g))
              J)
          (@Inv.inv
            (@Matrix.GeneralLinearGroup n A inst_2 inst_1 (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
            (@InvOneClass.toInv
              (@Matrix.GeneralLinearGroup n A inst_2 inst_1 (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
              (@DivInvOneMonoid.toInvOneClass
                (@Matrix.GeneralLinearGroup n A inst_2 inst_1
                  (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
                (@DivisionMonoid.toDivInvOneMonoid
                  (@Matrix.GeneralLinearGroup n A inst_2 inst_1
                    (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
                  (@Group.toDivisionMonoid
                    (@Matrix.GeneralLinearGroup n A inst_2 inst_1
                      (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
                    (@Units.instGroup (Matrix n n A)
                      (@Semiring.toMonoid (Matrix n n A)
                        (@Matrix.semiring n A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)) inst_1
                          inst_2)))))))
            g) := by sorry


















noncomputable def UpperTheory.Reformulated.B.Yzd4.UJ :
    {A : Type} →
      [inst : CommRing A] →
        {n : Type} →
          [inst_1 : Fintype n] →
            [inst_2 : DecidableEq n] →
              @RingHom A A (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
                  (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))) →
                Matrix n n A →
                  @Subgroup
                    (@Matrix.GeneralLinearGroup n A inst_2 inst_1
                      (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
                    (@Units.instGroup (Matrix n n A)
                      (@Semiring.toMonoid (Matrix n n A)
                        (@Matrix.semiring n A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)) inst_1
                          inst_2))) := sorry











































































theorem UpperTheory.Reformulated.B.Yzd4.aux6 :
    ∀ {F : Type} [inst : Field F] (R : Type) [inst_1 : CommRing R]
      [inst_2 :
        @Algebra F R (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_1))],
      @SMulCommClass F F R
        (@SMulZeroClass.toSMul F R
          (@AddZero.toZero R
            (@AddZeroClass.toAddZero R
              (@AddMonoid.toAddZeroClass R
                (@AddCommMonoid.toAddMonoid R
                  (@Semiring.toAddCommMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_1)))))))
          (@DistribSMul.toSMulZeroClass F R
            (@AddMonoid.toAddZeroClass R
              (@AddCommMonoid.toAddMonoid R
                (@Semiring.toAddCommMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_1)))))
            (@DistribMulAction.toDistribSMul F R
              (@Semiring.toMonoid F (@CommSemiring.toSemiring F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))))
              (@AddCommMonoid.toAddMonoid R
                (@Semiring.toAddCommMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_1))))
              (@Module.toDistribMulAction F R
                (@CommSemiring.toSemiring F (@Semifield.toCommSemiring F (@Field.toSemifield F inst)))
                (@Semiring.toAddCommMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_1)))
                (@Algebra.toModule F R (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_1)) inst_2)))))
        (@SMulZeroClass.toSMul F R
          (@AddZero.toZero R
            (@AddZeroClass.toAddZero R
              (@AddMonoid.toAddZeroClass R
                (@AddCommMonoid.toAddMonoid R
                  (@Semiring.toAddCommMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_1)))))))
          (@DistribSMul.toSMulZeroClass F R
            (@AddMonoid.toAddZeroClass R
              (@AddCommMonoid.toAddMonoid R
                (@Semiring.toAddCommMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_1)))))
            (@DistribMulAction.toDistribSMul F R
              (@Semiring.toMonoid F (@CommSemiring.toSemiring F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))))
              (@AddCommMonoid.toAddMonoid R
                (@Semiring.toAddCommMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_1))))
              (@Module.toDistribMulAction F R
                (@CommSemiring.toSemiring F (@Semifield.toCommSemiring F (@Field.toSemifield F inst)))
                (@Semiring.toAddCommMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_1)))
                (@Algebra.toModule F R (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_1)) inst_2))))) := by sorry



theorem UpperTheory.Reformulated.B.Yzd4.aux7 :
    ∀ {F : Type} [inst : Field F] (R : Type) [inst_1 : CommRing R]
      [inst_2 :
        @Algebra F R (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_1))],
      @IsScalarTower F F R
        (@instSMulOfMul F
          (@MulOne.toMul F
            (@MulOneClass.toMulOne F
              (@Monoid.toMulOneClass F
                (@Semiring.toMonoid F
                  (@DivisionSemiring.toSemiring F (@Semifield.toDivisionSemiring F (@Field.toSemifield F inst))))))))
        (@SemigroupAction.toSMul F R
          (@Monoid.toSemigroup F
            (@Semiring.toMonoid F
              (@DivisionSemiring.toSemiring F (@Semifield.toDivisionSemiring F (@Field.toSemifield F inst)))))
          (@MulAction.toSemigroupAction F R
            (@Semiring.toMonoid F
              (@DivisionSemiring.toSemiring F (@Semifield.toDivisionSemiring F (@Field.toSemifield F inst))))
            (@DistribMulAction.toMulAction F R
              (@Semiring.toMonoid F
                (@DivisionSemiring.toSemiring F (@Semifield.toDivisionSemiring F (@Field.toSemifield F inst))))
              (@AddCommMonoid.toAddMonoid R
                (@Semiring.toAddCommMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_1))))
              (@Module.toDistribMulAction F R
                (@DivisionSemiring.toSemiring F (@Semifield.toDivisionSemiring F (@Field.toSemifield F inst)))
                (@Semiring.toAddCommMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_1)))
                (@Algebra.toModule F R (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_1)) inst_2)))))
        (@SemigroupAction.toSMul F R
          (@Monoid.toSemigroup F
            (@Semiring.toMonoid F
              (@DivisionSemiring.toSemiring F (@Semifield.toDivisionSemiring F (@Field.toSemifield F inst)))))
          (@MulAction.toSemigroupAction F R
            (@Semiring.toMonoid F
              (@DivisionSemiring.toSemiring F (@Semifield.toDivisionSemiring F (@Field.toSemifield F inst))))
            (@DistribMulAction.toMulAction F R
              (@Semiring.toMonoid F
                (@DivisionSemiring.toSemiring F (@Semifield.toDivisionSemiring F (@Field.toSemifield F inst))))
              (@AddCommMonoid.toAddMonoid R
                (@Semiring.toAddCommMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_1))))
              (@Module.toDistribMulAction F R
                (@DivisionSemiring.toSemiring F (@Semifield.toDivisionSemiring F (@Field.toSemifield F inst)))
                (@Semiring.toAddCommMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_1)))
                (@Algebra.toModule F R (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_1)) inst_2))))) := by sorry



noncomputable def UpperTheory.Reformulated.B.Yzd4.sigR :
    {F E : Type} →
      [inst : Field F] →
        [inst_1 : Field E] →
          [inst_2 :
              @Algebra F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))] →
            (R : Type) →
              [inst_3 : CommRing R] →
                [inst_4 :
                    @Algebra F R (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3))] →
                  @AlgHom F E E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))
                      inst_2 inst_2 →
                    @RingHom
                      (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst)) R E
                        (@Semiring.toAddCommMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)))
                        (@Semiring.toAddCommMonoid E
                          (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1))))
                        (@Algebra.toModule F R (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)) inst_4)
                        (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                          (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))
                          inst_2))
                      (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst)) R E
                        (@Semiring.toAddCommMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)))
                        (@Semiring.toAddCommMonoid E
                          (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1))))
                        (@Algebra.toModule F R (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)) inst_4)
                        (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                          (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))
                          inst_2))
                      (@Algebra.TensorProduct.instNonAssocSemiring F R E
                        (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                        (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)))
                        (@Algebra.toModule F R (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)) inst_4)
                        (@Algebra.to_smulCommClass F R (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)) inst_4)
                        (@IsScalarTower.right F R (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)) inst_4)
                        (@Semiring.toNonAssocSemiring E
                          (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1))))
                        (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                          (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))
                          inst_2)
                        (@Algebra.to_smulCommClass F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                          (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))
                          inst_2)
                        (@IsScalarTower.right F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                          (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))
                          inst_2))
                      (@Algebra.TensorProduct.instNonAssocSemiring F R E
                        (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                        (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)))
                        (@Algebra.toModule F R (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)) inst_4)
                        (@Algebra.to_smulCommClass F R (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)) inst_4)
                        (@IsScalarTower.right F R (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)) inst_4)
                        (@Semiring.toNonAssocSemiring E
                          (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1))))
                        (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                          (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))
                          inst_2)
                        (@Algebra.to_smulCommClass F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                          (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))
                          inst_2)
                        (@IsScalarTower.right F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                          (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))
                          inst_2)) := sorry


























































theorem UpperTheory.Reformulated.B.Yzd4.aux9 :
    ∀ {F : Type} [inst : Field F] (R : Type) [inst_1 : CommRing R]
      [inst_2 :
        @Algebra F R (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_1))],
      @SMulCommClass F R R
        (@Algebra.toSMul F R (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_1)) inst_2)
        (@instSMulOfMul R
          (@Distrib.toMul R (@instDistribOfSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_1))))) := by sorry



theorem UpperTheory.Reformulated.B.Yzd4.laurent_T_neg_one_mul_T_one :
    ∀ {F : Type} [inst : Field F] (R : Type) [inst_1 : CommRing R]
      [inst_2 :
        @Algebra F R (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_1))],
      @IsScalarTower F R R
        (@Algebra.toSMul F R (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_1)) inst_2)
        (@instSMulOfMul R
          (@Distrib.toMul R (@instDistribOfSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_1)))))
        (@Algebra.toSMul F R (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_1)) inst_2) := by sorry



theorem UpperTheory.Reformulated.B.Yzd4.aux11 :
    ∀ {F E : Type} [inst : Field F] [inst_1 : Field E]
      [inst_2 :
        @Algebra F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
          (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))],
      @SMulCommClass F E E
        (@Algebra.toSMul F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
          (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1))) inst_2)
        (@instSMulOfMul E
          (@Distrib.toMul E
            (@instDistribOfSemiring E
              (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))))) := by sorry



theorem UpperTheory.Reformulated.B.Yzd4.aux12 :
    ∀ {F E : Type} [inst : Field F] [inst_1 : Field E]
      [inst_2 :
        @Algebra F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
          (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))],
      @IsScalarTower F E E
        (@Algebra.toSMul F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
          (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1))) inst_2)
        (@instSMulOfMul E
          (@Distrib.toMul E
            (@instDistribOfSemiring E
              (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1))))))
        (@Algebra.toSMul F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
          (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1))) inst_2) := by sorry



noncomputable def UpperTheory.Reformulated.B.Yzd4.inclR :
    {F E : Type} →
      [inst : Field F] →
        [inst_1 : Field E] →
          [inst_2 :
              @Algebra F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))] →
            (R : Type) →
              [inst_3 : CommRing R] →
                [inst_4 :
                    @Algebra F R (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3))] →
                  @RingHom E
                    (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst)) R E
                      (@Semiring.toAddCommMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)))
                      (@Semiring.toAddCommMonoid E
                        (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1))))
                      (@Algebra.toModule F R (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                        (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)) inst_4)
                      (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                        (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))
                        inst_2))
                    (@Semiring.toNonAssocSemiring E
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1))))
                    (@Algebra.TensorProduct.instNonAssocSemiring F R E
                      (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)))
                      (@Algebra.toModule F R (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                        (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)) inst_4)
                      (@Algebra.to_smulCommClass F R (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                        (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)) inst_4)
                      (@IsScalarTower.right F R (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                        (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)) inst_4)
                      (@Semiring.toNonAssocSemiring E
                        (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1))))
                      (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                        (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))
                        inst_2)
                      (@Algebra.to_smulCommClass F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                        (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))
                        inst_2)
                      (@IsScalarTower.right F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                        (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))
                        inst_2)) := sorry






























noncomputable def UpperTheory.Reformulated.B.Yzd4.JR :
    {F E : Type} →
      [inst : Field F] →
        [inst_1 : Field E] →
          [inst_2 :
              @Algebra F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))] →
            (R : Type) →
              [inst_3 : CommRing R] →
                [inst_4 :
                    @Algebra F R (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3))] →
                  {M : Nat} →
                    Matrix (Fin M) (Fin M) E →
                      Matrix (Fin M) (Fin M)
                        (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst)) R E
                          (@Semiring.toAddCommMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)))
                          (@Semiring.toAddCommMonoid E
                            (@DivisionSemiring.toSemiring E
                              (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1))))
                          (@Algebra.toModule F R (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                            (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)) inst_4)
                          (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                            (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))
                            inst_2)) := sorry










































































noncomputable def UpperTheory.Reformulated.B.Yzd4.HR :
    {F E : Type} →
      [inst : Field F] →
        [inst_1 : Field E] →
          [inst_2 :
              @Algebra F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))] →
            (R : Type) →
              [inst_3 : CommRing R] →
                [inst_4 :
                    @Algebra F R (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3))] →
                  @AlgHom F E E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))
                      inst_2 inst_2 →
                    {M : Nat} →
                      Matrix (Fin M) (Fin M) E →
                        @Subgroup
                          (@Matrix.GeneralLinearGroup (Fin M)
                            (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst)) R E
                              (@Semiring.toAddCommMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)))
                              (@Semiring.toAddCommMonoid E
                                (@DivisionSemiring.toSemiring E
                                  (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1))))
                              (@Algebra.toModule F R (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                                (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)) inst_4)
                              (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                                (@DivisionSemiring.toSemiring E
                                  (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))
                                inst_2))
                            (instDecidableEqFin M) (Fin.fintype M)
                            (@Algebra.TensorProduct.instSemiring F R E
                              (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                              (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)) inst_4
                              (@DivisionSemiring.toSemiring E
                                (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))
                              inst_2))
                          (@Units.instGroup
                            (Matrix (Fin M) (Fin M)
                              (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst)) R E
                                (@Semiring.toAddCommMonoid R
                                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)))
                                (@Semiring.toAddCommMonoid E
                                  (@DivisionSemiring.toSemiring E
                                    (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1))))
                                (@Algebra.toModule F R (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)) inst_4)
                                (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                                  (@DivisionSemiring.toSemiring E
                                    (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))
                                  inst_2)))
                            (@Semiring.toMonoid
                              (Matrix (Fin M) (Fin M)
                                (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst)) R E
                                  (@Semiring.toAddCommMonoid R
                                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)))
                                  (@Semiring.toAddCommMonoid E
                                    (@DivisionSemiring.toSemiring E
                                      (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1))))
                                  (@Algebra.toModule F R (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)) inst_4)
                                  (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                                    (@DivisionSemiring.toSemiring E
                                      (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))
                                    inst_2)))
                              (@Matrix.semiring (Fin M)
                                (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst)) R E
                                  (@Semiring.toAddCommMonoid R
                                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)))
                                  (@Semiring.toAddCommMonoid E
                                    (@DivisionSemiring.toSemiring E
                                      (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1))))
                                  (@Algebra.toModule F R (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)) inst_4)
                                  (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                                    (@DivisionSemiring.toSemiring E
                                      (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))
                                    inst_2))
                                (@Algebra.TensorProduct.instSemiring F R E
                                  (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)) inst_4
                                  (@DivisionSemiring.toSemiring E
                                    (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))
                                  inst_2)
                                (Fin.fintype M) (instDecidableEqFin M)))) := sorry



























noncomputable def UpperTheory.Reformulated.B.Yzd4.HA :
    {F E : Type} →
      [inst : Field F] →
        [inst_1 : Field E] →
          [inst_2 :
              @Algebra F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))] →
            (R : Type) →
              [inst_3 : CommRing R] →
                [@Algebra F R (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3))] →
                  @AlgHom F E E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))
                      inst_2 inst_2 →
                    {M : Nat} → Matrix (Fin M) (Fin M) E → Type := sorry















noncomputable def UpperTheory.Reformulated.B.Yzd4.topTens :
    {F E : Type} →
      [inst : Field F] →
        [inst_1 : Field E] →
          [inst_2 :
              @Algebra F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))] →
            (R : Type) →
              [inst_3 : CommRing R] →
                [inst_4 :
                    @Algebra F R (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3))] →
                  [TopologicalSpace R] →
                    TopologicalSpace
                      (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst)) R E
                        (@Semiring.toAddCommMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)))
                        (@Semiring.toAddCommMonoid E
                          (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1))))
                        (@Algebra.toModule F R (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)) inst_4)
                        (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                          (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))
                          inst_2)) := sorry








































noncomputable def UpperTheory.Reformulated.B.Yzd4.d18 :
    {F E : Type} →
      [inst : Field F] →
        [inst_1 : Field E] →
          [inst_2 :
              @Algebra F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))] →
            (R : Type) →
              [inst_3 : CommRing R] →
                [inst_4 :
                    @Algebra F R (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3))] →
                  (σ :
                      @AlgHom F E E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                        (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))
                        (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))
                        inst_2 inst_2) →
                    {M : Nat} →
                      (J : Matrix (Fin M) (Fin M) E) →
                        [TopologicalSpace R] →
                          Set (@UpperTheory.Reformulated.B.Yzd4.HA F E inst inst_1 inst_2 R inst_3 inst_4 σ M J) → Prop := sorry








































































































































































































































































































































































theorem UpperTheory.Reformulated.B.Yzd4.blockM_one_partner_eq_one :
    ∀ {F E : Type} [inst : Field F] [inst_1 : Field E]
      [inst_2 :
        @Algebra F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
          (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))]
      (R : Type) [inst_3 : CommRing R]
      [inst_4 :
        @Algebra F R (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3))]
      (σ :
        @AlgHom F E E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
          (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))
          (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1))) inst_2 inst_2)
      {M : Nat} (J : Matrix (Fin M) (Fin M) E) [inst_5 : TopologicalSpace R],
      @UpperTheory.Reformulated.B.Yzd4.d18 F E inst inst_1 inst_2 R inst_3 inst_4 σ M J inst_5
        (@Set.univ (@UpperTheory.Reformulated.B.Yzd4.HA F E inst inst_1 inst_2 R inst_3 inst_4 σ M J)) := by sorry




theorem UpperTheory.Reformulated.B.Yzd4.blockM_mul_alt :
    ∀ {F E : Type} [inst : Field F] [inst_1 : Field E]
      [inst_2 :
        @Algebra F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
          (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))]
      (R : Type) [inst_3 : CommRing R]
      [inst_4 :
        @Algebra F R (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3))]
      (σ :
        @AlgHom F E E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
          (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))
          (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1))) inst_2 inst_2)
      {M : Nat} (J : Matrix (Fin M) (Fin M) E) [inst_5 : TopologicalSpace R]
      (s t : Set (@UpperTheory.Reformulated.B.Yzd4.HA F E inst inst_1 inst_2 R inst_3 inst_4 σ M J)),
      @UpperTheory.Reformulated.B.Yzd4.d18 F E inst inst_1 inst_2 R inst_3 inst_4 σ M J inst_5 s →
        @UpperTheory.Reformulated.B.Yzd4.d18 F E inst inst_1 inst_2 R inst_3 inst_4 σ M J inst_5 t →
          @UpperTheory.Reformulated.B.Yzd4.d18 F E inst inst_1 inst_2 R inst_3 inst_4 σ M J inst_5
            (@Inter.inter (Set (@UpperTheory.Reformulated.B.Yzd4.HA F E inst inst_1 inst_2 R inst_3 inst_4 σ M J))
              (@Set.instInter (@UpperTheory.Reformulated.B.Yzd4.HA F E inst inst_1 inst_2 R inst_3 inst_4 σ M J)) s t) := by sorry






theorem UpperTheory.Reformulated.B.Yzd4.conj_invariant_character_mem :
    ∀ {F E : Type} [inst : Field F] [inst_1 : Field E]
      [inst_2 :
        @Algebra F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
          (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))]
      (R : Type) [inst_3 : CommRing R]
      [inst_4 :
        @Algebra F R (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3))]
      (σ :
        @AlgHom F E E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
          (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))
          (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1))) inst_2 inst_2)
      {M : Nat} (J : Matrix (Fin M) (Fin M) E) [inst_5 : TopologicalSpace R]
      (s : Set (Set (@UpperTheory.Reformulated.B.Yzd4.HA F E inst inst_1 inst_2 R inst_3 inst_4 σ M J))),
      (∀ (t : Set (@UpperTheory.Reformulated.B.Yzd4.HA F E inst inst_1 inst_2 R inst_3 inst_4 σ M J)),
          @Membership.mem (Set (@UpperTheory.Reformulated.B.Yzd4.HA F E inst inst_1 inst_2 R inst_3 inst_4 σ M J))
              (Set (Set (@UpperTheory.Reformulated.B.Yzd4.HA F E inst inst_1 inst_2 R inst_3 inst_4 σ M J)))
              (@Set.instMembership (Set (@UpperTheory.Reformulated.B.Yzd4.HA F E inst inst_1 inst_2 R inst_3 inst_4 σ M J))) s t →
            @UpperTheory.Reformulated.B.Yzd4.d18 F E inst inst_1 inst_2 R inst_3 inst_4 σ M J inst_5 t) →
        @UpperTheory.Reformulated.B.Yzd4.d18 F E inst inst_1 inst_2 R inst_3 inst_4 σ M J inst_5
          (@Set.sUnion (@UpperTheory.Reformulated.B.Yzd4.HA F E inst inst_1 inst_2 R inst_3 inst_4 σ M J) s) := by sorry













@[reducible] noncomputable def UpperTheory.Reformulated.B.Yzd4.instTopologicalSpaceHA :
    {F E : Type} →
      [inst : Field F] →
        [inst_1 : Field E] →
          [inst_2 :
              @Algebra F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))] →
            (R : Type) →
              [inst_3 : CommRing R] →
                [inst_4 :
                    @Algebra F R (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3))] →
                  (σ :
                      @AlgHom F E E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                        (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))
                        (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))
                        inst_2 inst_2) →
                    {M : Nat} →
                      (J : Matrix (Fin M) (Fin M) E) →
                        [TopologicalSpace R] →
                          TopologicalSpace (@UpperTheory.Reformulated.B.Yzd4.HA F E inst inst_1 inst_2 R inst_3 inst_4 σ M J) := sorry


















attribute [local instance] UpperTheory.Reformulated.B.Yzd4.instTopologicalSpaceHA

private theorem closed_UJ {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [T2Space A] {n : Type} [Fintype n] [DecidableEq n] (σ : A →+* A) (hσ : Continuous σ)
    (J : Matrix n n A) :
    IsClosed ((UpperTheory.Reformulated.B.Yzd4.UJ σ J : Subgroup (Matrix.GeneralLinearGroup n A)) :
      Set (Matrix.GeneralLinearGroup n A)) := by sorry








private theorem lcsc_GL {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [T2Space A] [LocallyCompactSpace A] [SecondCountableTopology A] {n : Type} [Fintype n]
    [DecidableEq n] :
    LocallyCompactSpace (Matrix.GeneralLinearGroup n A) ∧
      SecondCountableTopology (Matrix.GeneralLinearGroup n A) ∧
      T2Space (Matrix.GeneralLinearGroup n A) := by sorry









private theorem lcsc_sub {G : Type} [Group G] [TopologicalSpace G] (H : Subgroup G)
    (hH : IsClosed (H : Set G)) [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] :
    LocallyCompactSpace H ∧ SecondCountableTopology H ∧ T2Space H := by sorry



private theorem props_of_free {R D : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [Ring D] [Algebra R D]
    {ι : Type} [Fintype ι] (B : Module.Basis ι R D) [Module.Finite R D] [TopologicalSpace D]
    [IsModuleTopology R D] :
    IsTopologicalRing D ∧ LocallyCompactSpace D ∧ SecondCountableTopology D ∧ T2Space D := by sorry









private theorem tens_props (F E : Type) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
    [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R]
    [TopologicalSpace (TensorProduct F R E)] [IsModuleTopology R (TensorProduct F R E)] :
    IsTopologicalRing (TensorProduct F R E) ∧ LocallyCompactSpace (TensorProduct F R E) ∧
      SecondCountableTopology (TensorProduct F R E) ∧ T2Space (TensorProduct F R E) := by sorry


private theorem sigR_continuous {F E : Type} [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    [IsTopologicalRing R] [TopologicalSpace (TensorProduct F R E)]
    [IsModuleTopology R (TensorProduct F R E)] (σ : E →ₐ[F] E) :
    Continuous (UpperTheory.Reformulated.B.Yzd4.sigR R σ) := by sorry











theorem UpperTheory.Reformulated.B.Yzd4.lcsc_HA :
    ∀ {F E : Type} [inst : Field F] [inst_1 : Field E]
      [inst_2 :
        @Algebra F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
          (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))]
      [@FiniteDimensional F E (@Field.toDivisionRing F inst)
          (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_1)))
          (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
            (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1))) inst_2)]
      (R : Type) [inst_4 : CommRing R]
      [inst_5 :
        @Algebra F R (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_4))]
      [inst_6 : TopologicalSpace R]
      [@IsTopologicalRing R inst_6
          (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing R
            (@NonUnitalCommRing.toNonUnitalNonAssocCommRing R (@CommRing.toNonUnitalCommRing R inst_4)))]
      [@LocallyCompactSpace R inst_6] [@SecondCountableTopology R inst_6] [@T2Space R inst_6]
      (σ :
        @AlgHom F E E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
          (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))
          (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1))) inst_2 inst_2)
      (M : Nat) (J : Matrix (Fin M) (Fin M) E),
      And
        (@LocallyCompactSpace (@UpperTheory.Reformulated.B.Yzd4.HA F E inst inst_1 inst_2 R inst_4 inst_5 σ M J)
          (@UpperTheory.Reformulated.B.Yzd4.instTopologicalSpaceHA F E inst inst_1 inst_2 R inst_4 inst_5 σ M J inst_6))
        (And
          (@SecondCountableTopology (@UpperTheory.Reformulated.B.Yzd4.HA F E inst inst_1 inst_2 R inst_4 inst_5 σ M J)
            (@UpperTheory.Reformulated.B.Yzd4.instTopologicalSpaceHA F E inst inst_1 inst_2 R inst_4 inst_5 σ M J inst_6))
          (@T2Space (@UpperTheory.Reformulated.B.Yzd4.HA F E inst inst_1 inst_2 R inst_4 inst_5 σ M J)
            (@UpperTheory.Reformulated.B.Yzd4.instTopologicalSpaceHA F E inst inst_1 inst_2 R inst_4 inst_5 σ M J inst_6))) := by sorry














