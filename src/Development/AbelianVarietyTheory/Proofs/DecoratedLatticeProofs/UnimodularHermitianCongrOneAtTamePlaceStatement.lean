module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsEqTransposeMulMapOfIdempotent
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CharConjFixedEqOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittCoreEmbeddingPreservesSupportedUnitarySubgro
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralTraceIdempotentAtTamePlace
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNormOfConjFixedUnitTamePlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSelfDualLatticeAtPlaceComapUnitarySupported
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittLeviTransvectionMemCompactAtPlace
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjFixedIntegralIsUnitOrIdemSubUnit

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix

noncomputable section
open IsDedekindDomain NumberField
open scoped TensorProduct




namespace GlobalTheory.IwaFixed

open GlobalTheory.FinPlLoc

variable {D : D7}

theorem evalV_single_same (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v) :
    evalV F v (singleV F v y) = y := by
  classical
  exact RestrictedProduct.single_eq_same (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v y

theorem evalV_single_ne (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v)
    {w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) : evalV F w (singleV F v y) = 0 := by
  classical
  exact RestrictedProduct.single_eq_of_ne (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) y h

def intIn (D : D7) (v : Pl D) : v.adicCompletionIntegers D.host.F →+* Fv D.host.F v ⊗[D.host.F] D.host.E :=
  (algebraMap (Fv D.host.F v) (Fv D.host.F v ⊗[D.host.F] D.host.E)).comp (algebraMap _ (Fv D.host.F v))

theorem integral_compFin (v : Pl D) {z : Af D.host.F ⊗[D.host.F] D.host.E} (hz : z ∈ intAE D) :
    (intIn D v).IsIntegralElem (GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D v z) := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, o, rfl⟩ := hz
    have e : GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D v (a ⊗ₜ[D.host.F] (o : D.host.E)) =
        intIn D v ⟨evalV D.host.F v a, ha v⟩ *
          (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Fv D.host.F v ⊗[D.host.F] D.host.E) (o : D.host.E) := by
      show Algebra.TensorProduct.map (evalV D.host.F v) (AlgHom.id _ _) (a ⊗ₜ[D.host.F] (o : D.host.E)) =
        (evalV D.host.F v a ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : Fv D.host.F v) ⊗ₜ[D.host.F] (o : D.host.E))
      rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rfl
    rw [e]
    refine RingHom.IsIntegralElem.mul _ (RingHom.isIntegralElem_map _) ?_
    obtain ⟨p, hp, hpo⟩ : IsIntegral ℤ (o : D.host.E) := o.2
    refine ⟨p.map (Int.castRingHom _), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have h := congrArg (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Fv D.host.F v ⊗[D.host.F] D.host.E).toRingHom hpo
    rw [Polynomial.hom_eval₂, map_zero] at h
    rw [RingHom.ext_int ((intIn D v).comp (Int.castRingHom _)) ((Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Fv D.host.F v ⊗[D.host.F] D.host.E).toRingHom.comp (algebraMap ℤ D.host.E))]
    exact h
  | zero => rw [map_zero]; exact RingHom.isIntegralElem_zero _
  | add z z' _ _ h h' => rw [map_add (f := _)]; exact RingHom.IsIntegralElem.add _ h h'
  | neg z _ h => rw [map_neg]; exact RingHom.IsIntegralElem.neg _ h

theorem mem_int_of_integral (v : Pl D) (a : Fv D.host.F v)
    (h : (intIn D v).IsIntegralElem (a ⊗ₜ[D.host.F] (1 : D.host.E))) : a ∈ v.adicCompletionIntegers D.host.F := by
  obtain ⟨p, hp, hpa⟩ := h
  have hinj : Function.Injective (algebraMap (Fv D.host.F v) (Fv D.host.F v ⊗[D.host.F] D.host.E)) :=
    RingHom.injective _
  have hi : IsIntegral (v.adicCompletionIntegers D.host.F) a := by
    refine ⟨p, hp, hinj ?_⟩
    rw [Polynomial.hom_eval₂, map_zero]
    exact hpa
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
  rw [← hy]
  exact y.2

theorem exists_inv (v : Pl D) {x : AE D} (hx : x ∈ idAt D (· = v)) (u : (v.adicCompletionIntegers D.host.F)ˣ)
    (hu : compAt D v x = ((u : v.adicCompletionIntegers D.host.F) : Fv D.host.F v) ⊗ₜ[D.host.F] (1 : D.host.E)) :
    ∃ y ∈ intAt D (· = v), x * y = idem D (· = v) := by
  classical
  obtain ⟨c, hci, hc⟩ : ∃ c : Fv D.host.F v, c ∈ v.adicCompletionIntegers D.host.F ∧ (u.val.1 : Fv D.host.F v) * c = 1 :=
    ⟨u.inv.1, u.inv.2, congrArg Subtype.val u.val_inv⟩
  refine ⟨pairA D.host.F 0 (singleV D.host.F v c) ⊗ₜ[D.host.F] (1 : D.host.E), ⟨?_, ?_⟩, ?_⟩
  · exact pair_mem_idAt _ _ (fun w hw => evalV_single_ne _ v c hw) _
  · rw [finPart_pair]
    refine AddSubgroup.subset_closure ⟨singleV D.host.F v c, fun w => ?_, 1, rfl⟩
    by_cases hw : w = v
    · subst hw; rw [evalV_single_same]; exact hci
    · rw [evalV_single_ne _ v c hw]; exact zero_mem _
  · rw [← sub_eq_zero]
    apply eq_zero_of_comp
    · rw [map_sub, map_mul, infPart_of_idAt hx, infPart_of_idAt (idem_mem_idAt _), zero_mul, sub_zero]
    · intro w
      rw [map_sub, map_mul, compAt_idem]
      by_cases hw : w = v
      · subst hw
        rw [hu, compAt_pair, evalV_single_same, if_pos rfl, Algebra.TensorProduct.tmul_mul_tmul, mul_one, hc,
          ← Algebra.TensorProduct.one_def, sub_self]
      · rw [compAt_of_idAt hx hw, if_neg hw, zero_mul, sub_zero]

theorem fixed_unit_or : ∀ (D : D7) (v : Pl D) (ε : AE D), Tame D v → ε * ε = ε → cA D ε = ε → ε ∈ intAt D (· = v) →
    (∀ a, a ∈ idAt D (· = v) ↔ ε * a = a) → ∀ x ∈ intAt D (· = v), cA D x = x →
    (∃ y ∈ intAt D (· = v), x * y = ε) ∨ (∃ y ∈ intAt D (· = v), (ε - x) * y = ε) := by
  intro D v ε _ _ _ hε hid x hx hfix
  classical
  have hεe : ε = idem D (· = v) := by
    have h1 := (hid _).1 (idem_mem_idAt (· = v))
    have h2 := (mem_idAt_iff (· = v) ε).1 hε.1
    rw [← h2, mul_comm, h1]
  subst hεe
  obtain ⟨b, hb⟩ := GlobalTheory.CharConjFixed.fixed_mem D x hfix
  have hcomp : compAt D v x = evalV D.host.F v (sndA D.host.F b) ⊗ₜ[D.host.F] (1 : D.host.E) := by
    rw [← hb]
    show Algebra.TensorProduct.map (evalV D.host.F v) (AlgHom.id _ _)
      (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id _ _) (b ⊗ₜ[D.host.F] (1 : D.host.E))) = _
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]
    rfl
  have hint : evalV D.host.F v (sndA D.host.F b) ∈ v.adicCompletionIntegers D.host.F := by
    apply mem_int_of_integral
    rw [← hcomp]
    exact integral_compFin v hx.2
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (⟨_, hint⟩ : v.adicCompletionIntegers D.host.F) with ⟨u, hu⟩ | ⟨u, hu⟩
  · left
    refine exists_inv v hx.1 u ?_
    rw [hu, hcomp]
  · right
    refine exists_inv v (sub_mem (idem_mem_idAt _) hx.1) u ?_
    rw [hu, map_sub, compAt_idem, if_pos rfl, hcomp, Algebra.TensorProduct.one_def, ← TensorProduct.sub_tmul]
    rfl

end GlobalTheory.IwaFixed

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjFixedIntegralIsUnitOrIdemSubUnitStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix

theorem _root_.GlobalTheory.T.conjFixed_integral_isUnit_or_idem_sub_unit : ∀ (D : D7) (v : Pl D) (ε : AE D), Tame D v → ε * ε = ε → cA D ε = ε → ε ∈ intAt D (· = v) → (∀ a, a ∈ idAt D (· = v) ↔ ε * a = a) → ∀ x ∈ intAt D (· = v), cA D x = x → (∃ y ∈ intAt D (· = v), x * y = ε) ∨ (∃ y ∈ intAt D (· = v), (ε - x) * y = ε) := by
  first | exact @GlobalTheory.IwaFixed.fixed_unit_or | exact GlobalTheory.IwaFixed.fixed_unit_or | (intros; apply GlobalTheory.IwaFixed.fixed_unit_or <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnimodularHermitianCongrOneAtTamePlace

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix

namespace GlobalTheory.IwaPlace.UnimodNF

section Abstract

variable {A : Type*} [CommRing A] {ε : A} (hid : IsIdempotentElem ε) (O : Set A)
  (h0 : (0 : A) ∈ O) (hadd : ∀ a ∈ O, ∀ b ∈ O, a + b ∈ O) (hneg : ∀ a ∈ O, -a ∈ O)
  (hmul : ∀ a ∈ O, ∀ b ∈ O, a * b ∈ O) (hεO : ε ∈ O)

def sub : Subring hid.Corner where
  carrier := {x | x.1 ∈ O}
  zero_mem' := h0
  add_mem' {x y} hx hy := hadd _ hx _ hy
  neg_mem' {x} hx := hneg _ hx
  mul_mem' {x y} hx hy := hmul _ hx _ hy
  one_mem' := hεO


include hid h0 hadd hneg hmul hεO in
theorem exists_congr_one (c : A →+* A) (hc : ∀ x, c (c x) = x) (hcO : ∀ a ∈ O, c a ∈ O) (hcε : c ε = ε)
    (hεa : ∀ a ∈ O, ε * a = a)
    (hloc : ∀ x ∈ O, c x = x → (∃ y ∈ O, x * y = ε) ∨ (∃ y ∈ O, (ε - x) * y = ε))
    (hw : ∃ w ∈ O, w + c w = ε)
    (hnorm : ∀ u ∈ O, c u = u → (∃ y ∈ O, u * y = ε) → ∃ x ∈ O, x * c x = u)
    {n : ℕ} (H : Matrix (Fin n) (Fin n) A) (hH : ∀ i j, H i j ∈ O) (hherm : ∀ i j, c (H i j) = H j i)
    (hinv : ∃ H' : Matrix (Fin n) (Fin n) A, (∀ i j, H' i j ∈ O) ∧ H * H' = ε • (1 : Matrix (Fin n) (Fin n) A)) :
    ∃ P P' : Matrix (Fin n) (Fin n) A, (∀ i j, P i j ∈ O) ∧ (∀ i j, P' i j ∈ O) ∧
      P * P' = ε • (1 : Matrix (Fin n) (Fin n) A) ∧ P' * P = ε • (1 : Matrix (Fin n) (Fin n) A) ∧
      (P.map c)ᵀ * (H * P) = ε • (1 : Matrix (Fin n) (Fin n) A) := by
  classical
  let R := sub hid O h0 hadd hneg hmul hεO
  have corner_mem : ∀ a ∈ O, a ∈ Subsemigroup.corner ε := fun a ha =>
    (Subsemigroup.mem_corner_iff hid).2 ⟨hεa a ha, by rw [mul_comm]; exact hεa a ha⟩
  let mk : ∀ a, a ∈ O → R := fun a ha => ⟨⟨a, corner_mem a ha⟩, ha⟩
  let val : R →+ A := { toFun := fun x => x.1.1, map_zero' := rfl, map_add' := fun _ _ => rfl }
  have val_mem : ∀ x : R, val x ∈ O := fun x => x.2
  have val_inj : ∀ x y : R, val x = val y → x = y := fun x y h => Subtype.ext (Subtype.ext h)
  let c' : R →+* R :=
    { toFun := fun x => mk (c (val x)) (hcO _ (val_mem x))
      map_one' := val_inj _ _ (show c ε = ε from hcε)
      map_mul' := fun x y => val_inj _ _ (show c (val x * val y) = c (val x) * c (val y) from map_mul c _ _)
      map_zero' := val_inj _ _ (show c 0 = 0 from map_zero c)
      map_add' := fun x y => val_inj _ _ (show c (val x + val y) = c (val x) + c (val y) from map_add c _ _) }
  have hc' : ∀ x, c' (c' x) = x := fun x => val_inj _ _ (show c (c (val x)) = val x from hc _)
  have map_mul_val : ∀ X Y : Matrix (Fin n) (Fin n) R, (X * Y).map val = X.map val * Y.map val := by
    intro X Y
    ext i j

    simp only [Matrix.map_apply, Matrix.mul_apply, map_sum]
    rfl
  have map_one_val : (1 : Matrix (Fin n) (Fin n) R).map val = ε • (1 : Matrix (Fin n) (Fin n) A) := by
    ext i j
    rw [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.one_apply]
    split_ifs
    · simp only [smul_eq_mul, mul_one]; rfl
    · simp only [smul_eq_mul, mul_zero, map_zero]
  have map_inj : ∀ X Y : Matrix (Fin n) (Fin n) R, X.map val = Y.map val → X = Y := fun X Y h =>
    Matrix.ext fun i j => val_inj _ _ (congrFun (congrFun h i) j)
  let G : Matrix (Fin n) (Fin n) R := Matrix.of fun i j => mk (H i j) (hH i j)
  have hGH : G.map val = H := by ext i j; rfl
  obtain ⟨H', hH'O, hHH'⟩ := hinv
  let G' : Matrix (Fin n) (Fin n) R := Matrix.of fun i j => mk (H' i j) (hH'O i j)
  have hG'H : G'.map val = H' := by ext i j; rfl
  have hGG' : G * G' = 1 := map_inj _ _ (by rw [map_mul_val, map_one_val, hGH, hG'H]; exact hHH')
  have hdet : IsUnit G.det := Matrix.isUnit_det_of_right_inverse hGG'
  have hG : ∀ a b, c' (G a b) = G b a := fun a b => val_inj _ _ (hherm a b)
  have hlocR : ∀ x : R, c' x = x → IsUnit x ∨ IsUnit (1 - x) := by
    intro x hx
    have hx' : c (val x) = val x := congrArg val hx
    rcases hloc (val x) (val_mem x) hx' with ⟨y, hy, hxy⟩ | ⟨y, hy, hxy⟩
    · exact Or.inl (isUnit_iff_exists_inv.2 ⟨mk y hy, val_inj _ _ hxy⟩)
    · exact Or.inr (isUnit_iff_exists_inv.2 ⟨mk y hy, val_inj _ _ hxy⟩)
  have hwR : ∃ w : R, w + c' w = 1 := by
    obtain ⟨w, hw, hw'⟩ := hw
    exact ⟨mk w hw, val_inj _ _ hw'⟩
  have hnormR : ∀ u : R, c' u = u → IsUnit u → ∃ x, x * c' x = u := by
    intro u hu hu'
    obtain ⟨y, hy⟩ := hu'.exists_right_inv
    obtain ⟨x, hx, hx'⟩ := hnorm (val u) (val_mem u) (congrArg val hu) ⟨val y, val_mem y, congrArg val hy⟩
    exact ⟨mk x hx, val_inj _ _ hx'⟩
  obtain ⟨Q, hQ, hGQ⟩ :=
    GlobalTheory.UnramifiedHermitian.exists_eq_transpose_mul_map_of_isUnit_or c' hc' hlocR hwR hnormR hG hdet
  have hmap1 : (1 : Matrix (Fin n) (Fin n) R).map c' = 1 := Matrix.map_one _ (map_zero c') (map_one c')
  refine ⟨((Q⁻¹).map c').map val, (Q.map c').map val, fun i j => val_mem _, fun i j => val_mem _, ?_, ?_, ?_⟩
  · rw [← map_mul_val, ← Matrix.map_mul, Matrix.nonsing_inv_mul Q hQ, hmap1, map_one_val]
  · rw [← map_mul_val, ← Matrix.map_mul, Matrix.mul_nonsing_inv Q hQ, hmap1, map_one_val]
  · have e1 : (((Q⁻¹).map c').map val).map c = (Q⁻¹).map val := by
      ext i j
      exact congrArg val (hc' (Q⁻¹ i j))
    rw [e1, ← Matrix.transpose_map, ← hGH, ← map_mul_val, ← map_mul_val, ← map_one_val]
    congr 1
    have h1 : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q hQ
    rw [hGQ]
    calc (Q⁻¹)ᵀ * (Qᵀ * Q.map c' * (Q⁻¹).map c') = (Q * Q⁻¹)ᵀ * (Q * Q⁻¹).map c' := by
          rw [Matrix.transpose_mul, Matrix.map_mul]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h1, Matrix.transpose_one, hmap1, Matrix.one_mul]

end Abstract



variable {D : D7}

theorem intAt_zero' (P : Pl D → Prop) : (0 : AE D) ∈ intAt D P := ⟨zero_mem _, by rw [map_zero]; exact zero_mem _⟩

theorem intAt_neg' {P : Pl D → Prop} {a : AE D} (ha : a ∈ intAt D P) : -a ∈ intAt D P :=
  ⟨neg_mem ha.1, by rw [RingHom.map_neg]; exact neg_mem ha.2⟩

theorem cA_mem_intAt' {v : Pl D} {a : AE D} (ha : a ∈ intAt D (· = v)) : cA D a ∈ intAt D (· = v) :=
  ⟨GlobalTheory.FinPl.RootKeep.conj_mem_idAt ha.1, (GlobalTheory.FinPl.FrameLat.cA_int_iff a).2 ha.2⟩

theorem unimodular_congr_one : ∀ (D : D7) (v : Pl D) (ε : AE D) (n : ℕ) (H : Matrix (Fin n) (Fin n) (AE D)), Tame D v → ε * ε = ε → cA D ε = ε → ε ∈ intAt D (· = v) → (∀ a, a ∈ idAt D (· = v) ↔ ε * a = a) → (∀ i j, H i j ∈ intAt D (· = v)) → (∀ i j, cA D (H i j) = H j i) → (∃ H' : Matrix (Fin n) (Fin n) (AE D), (∀ i j, H' i j ∈ intAt D (· = v)) ∧ H * H' = ε • (1 : Matrix (Fin n) (Fin n) (AE D))) → ∃ P P' : Matrix (Fin n) (Fin n) (AE D), (∀ i j, P i j ∈ intAt D (· = v)) ∧ (∀ i j, P' i j ∈ intAt D (· = v)) ∧ P * P' = ε • (1 : Matrix (Fin n) (Fin n) (AE D)) ∧ P' * P = ε • (1 : Matrix (Fin n) (Fin n) (AE D)) ∧ adj P * (H * P) = ε • (1 : Matrix (Fin n) (Fin n) (AE D)) := by
  intro D v ε n H htame hεε hεc hεI hε hHI hherm hinv
  exact exists_congr_one (hid := hεε) (O := intAt D (· = v)) (intAt_zero' _)
    (fun a ha b hb => GlobalTheory.IwaPlace.SdComap.intAt_add ha hb) (fun a ha => intAt_neg' ha)
    (fun a ha b hb => GlobalTheory.IwaPlace.SdComap.intAt_mul ha hb) hεI (cA D) (fun z => Formalism.L2.Theta.cA_cA z)
    (fun a ha => cA_mem_intAt' ha) hεc (fun a ha => (hε a).1 ha.1)
    (GlobalTheory.T.conjFixed_integral_isUnit_or_idem_sub_unit D v ε htame hεε hεc hεI hε)
    (GlobalTheory.IwaPlace.exists_trace_one_at_tame D v ε hεε hεc hεI hε htame)
    (GlobalTheory.T.exists_norm_of_conjFixed_unit_tamePlace D v ε htame hεε hεc hεI hε) H hHI hherm hinv

end GlobalTheory.IwaPlace.UnimodNF

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnimodularHermitianCongrOneAtTamePlaceStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix

theorem _root_.GlobalTheory.T.unimodular_hermitian_congr_one_at_tamePlace : ∀ (D : D7) (v : Pl D) (ε : AE D) (n : ℕ) (H : Matrix (Fin n) (Fin n) (AE D)), Tame D v → ε * ε = ε → cA D ε = ε → ε ∈ intAt D (· = v) → (∀ a, a ∈ idAt D (· = v) ↔ ε * a = a) → (∀ i j, H i j ∈ intAt D (· = v)) → (∀ i j, cA D (H i j) = H j i) → (∃ H' : Matrix (Fin n) (Fin n) (AE D), (∀ i j, H' i j ∈ intAt D (· = v)) ∧ H * H' = ε • (1 : Matrix (Fin n) (Fin n) (AE D))) → ∃ P P' : Matrix (Fin n) (Fin n) (AE D), (∀ i j, P i j ∈ intAt D (· = v)) ∧ (∀ i j, P' i j ∈ intAt D (· = v)) ∧ P * P' = ε • (1 : Matrix (Fin n) (Fin n) (AE D)) ∧ P' * P = ε • (1 : Matrix (Fin n) (Fin n) (AE D)) ∧ adj P * (H * P) = ε • (1 : Matrix (Fin n) (Fin n) (AE D)) := by
  first | exact @GlobalTheory.IwaPlace.UnimodNF.unimodular_congr_one | exact GlobalTheory.IwaPlace.UnimodNF.unimodular_congr_one | (intros; apply GlobalTheory.IwaPlace.UnimodNF.unimodular_congr_one <;> assumption)
end
end
