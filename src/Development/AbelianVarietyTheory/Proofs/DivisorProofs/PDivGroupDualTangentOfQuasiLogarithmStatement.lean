module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffNmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffUpNmul
public import Development.AbelianVarietyTheory.Definitions.Divisors.KerIdealCompOfSurjective
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Definitions.Divisors.GhostFrobenius
import Mathlib.RingTheory.MvPowerSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvAtNmulPowSelf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupLawCoboundaryOneSubstOfEndomorphism
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaBaseChangeFiniteProjectiveReflexive
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupFormalChartEvNatMultipleEqConvPowerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicContinuousEvaluationExistsUniqueSubstNatura
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHausdorffOfProjective

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdSubOfDUnitEq

section

@[expose] public section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

namespace GlobalTheory.CotDualLin

theorem dvd_counit (O A : Type) [CommRing O] [CommRing A] [HopfAlgebra O A] [Module.Finite O A]
    [Module.Projective O A] (a : A) (q : O) (t : A ⊗[O] A)
    (h : Coalgebra.comul (R := O) a = a ⊗ₜ[O] (1 : A) + (1 : A) ⊗ₜ[O] a + q • t) :
    q ∣ Coalgebra.counit (R := O) a := by
  have h1 := CartierDual.mul_apply (R := O) (C := A) 1 1 a
  rw [one_mul, h] at h1
  simp only [map_add (f := _), map_smul, CartierDual.pair_tmul_tmul, CartierDual.one_apply, Bialgebra.counit_one] at h1
  exact ⟨-(CartierDual.pair O A A (1 ⊗ₜ 1) t), by rw [smul_eq_mul] at h1; linear_combination -h1⟩

theorem dvd_of_mem_sq (O A : Type) [CommRing O] [CommRing A] [HopfAlgebra O A] [Coalgebra.IsCocomm O A] [Module.Finite O A]
    [Module.Projective O A] (a : A) (q : O) (t : A ⊗[O] A)
    (h : Coalgebra.comul (R := O) a = a ⊗ₜ[O] (1 : A) + (1 : A) ⊗ₜ[O] a + q • t)
    (χ : CartierDual O A) (hχ : χ ∈ RingHom.ker (Bialgebra.counitAlgHom O (CartierDual O A)) ^ 2) :
    q ∣ χ a := by
  rw [pow_two] at hχ
  refine Submodule.mul_induction_on hχ (fun x hx y hy => ?_) (fun x y hx hy => ?_)
  · have hx1 : x 1 = 0 := hx
    have hy1 : y 1 = 0 := hy
    rw [CartierDual.mul_apply, h]
    simp only [map_add (f := _), map_smul, CartierDual.pair_tmul_tmul, hx1, hy1, mul_zero, zero_mul, zero_add, smul_eq_mul]
    exact dvd_mul_right _ _
  · have e : (x + y) a = x a + y a := rfl
    rw [e]; exact dvd_add hx hy

theorem dvd_sub_of_dUnit_eq : ∀ (O A : Type) [CommRing O] [CommRing A] [HopfAlgebra O A] [Coalgebra.IsCocomm O A]
    [Module.Finite O A] [Module.Projective O A] (a : A) (q : O) (t : A ⊗[O] A),
    Coalgebra.comul (R := O) a = a ⊗ₜ[O] (1 : A) + (1 : A) ⊗ₜ[O] a + q • t →
    ∀ φ ψ : CartierDual O A, PDiv.dUnit (R := O) φ = PDiv.dUnit (R := O) ψ → q ∣ φ a - ψ a := by
  intro O A _ _ _ _ _ _ a q t h φ ψ hd
  have h0 : PDiv.dUnit (R := O) (φ - ψ) = 0 := by rw [PDiv.dUnit, map_sub]; exact sub_eq_zero.2 hd
  rw [PDiv.dUnit, AugCot.d_eq_zero_iff] at h0
  have h2 := dvd_of_mem_sq O A a q t h _ h0
  set c := Bialgebra.counitAlgHom O (CartierDual O A) (φ - ψ)
  have h3 : (algebraMap O (CartierDual O A) c) a = c * Coalgebra.counit (R := O) a := by
    rw [Algebra.algebraMap_eq_smul_one]; rfl
  have e : (φ - ψ - algebraMap O (CartierDual O A) c) a = φ a - ψ a - (algebraMap O (CartierDual O A) c) a := rfl
  rw [e, h3] at h2
  have h4 := dvd_mul_of_dvd_right (dvd_counit O A a q t h) c
  have := dvd_add h2 h4
  rwa [sub_add_cancel] at this

end GlobalTheory.CotDualLin
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicCompleteRingOfModule

section

@[expose] public section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EvP

theorem isAdicComplete_ring_of_module {O A : Type} [CommRing O] [CommRing A] [Algebra O A]
    (p : ℕ) [h : IsAdicComplete (Ideal.span {(p : O)}) A] :
    IsAdicComplete (Ideal.span {(p : A)}) A := by
  have key : ∀ (n : ℕ) (x : A), x ∈ (Ideal.span {(p : A)} ^ n • ⊤ : Submodule A A) ↔
      x ∈ (Ideal.span {(p : O)} ^ n • ⊤ : Submodule O A) := by
    intro n x
    rw [GlobalTheory.mem_span_singleton_pow_smul_top_iff_exists, GlobalTheory.mem_span_singleton_pow_smul_top_iff_exists]
    simp [Algebra.smul_def]
  exact
    { haus' := fun x hx => IsHausdorff.haus h.toIsHausdorff x fun n =>
        SModEq.sub_mem.2 ((key n _).1 (SModEq.sub_mem.1 (hx n)))
      prec' := fun f hf => by
        obtain ⟨L, hL⟩ := IsPrecomplete.prec h.toIsPrecomplete (f := f) fun {m n} hmn =>
          SModEq.sub_mem.2 ((key _ _).1 (SModEq.sub_mem.1 (hf hmn)))
        exact ⟨L, fun n => SModEq.sub_mem.2 ((key _ _).2 (SModEq.sub_mem.1 (hL n)))⟩ }

theorem constantCoeff_nmul {O : Type} [CommRing O] {d : ℕ}
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O) (hμ : ∀ j, constantCoeff (μ j) = 0) :
    ∀ (k : ℕ) (j : Fin d), constantCoeff (nmul μ k j) = 0 := by
  intro k
  induction k with
  | zero => intro j; rfl
  | succ k ihk =>
    intro j
    have hsucc : nmul μ (k + 1) j =
        subst (Sum.elim (nmul μ k) fun i => (X i : MvPowerSeries (Fin d) O)) (μ j) := by
      simp only [nmul, Function.iterate_succ_apply']
      rfl
    rw [hsucc]
    refine constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero ?_) ?_ (hμ j) <;>
    · rintro (l | l)
      · simpa using ihk l
      · simp

theorem ev_subst_nmul_p : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (n : ℕ) (s : MvPowerSeries (Fin d) O), c.ev (n + 1) (subst (nmul c.μ p) s) = G.mulP n (c.ev n s) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv G d c n s
  haveI : IsAdicComplete (Ideal.span {(p : O)}) (G.A (n + 1)) :=
    GlobalTheory.isAdicComplete_of_finite_projective _ _
  haveI : IsAdicComplete (Ideal.span {(p : G.A (n + 1))}) (G.A (n + 1)) :=
    isAdicComplete_ring_of_module (O := O) p
  have hT := (GlobalTheory.CEval.continuous_eval p O (G.A (n + 1)) (Fin d) (c.x (n + 1)) (c.nil (n + 1))).2
    (c.ev (n + 1)) (c.isEval (n + 1))
  let E' : MvPowerSeries (Fin d) O →ₐ[O] G.A (n + 1) :=
    (G.mulP n : G.A n →ₐ[O] G.A (n + 1)).comp (c.ev n)
  have hu : ∀ j, constantCoeff (nmul c.μ p j) = 0 :=
    constantCoeff_nmul c.μ (fun j => c.isLaw.const j) p
  have hE' : IsEval p (fun j => c.ev (n + 1) (nmul c.μ p j)) E' := by
    constructor
    · intro j
      show G.mulP n (c.ev n (X j)) = c.ev (n + 1) (nmul c.μ p j)
      rw [(c.isEval n).1 j, GlobalTheory.T.pDivGroupFormalChart_ev_natMultiple_eq_convPower p C v O hv G d c (n + 1) p j, ← c.res n j, mulP_res]
    · intro m
      obtain ⟨N, hN⟩ := (c.isEval n).2 m
      refine ⟨N, fun f hf => ?_⟩
      have := map_dvd (G.mulP n : G.A n →ₐ[O] G.A (n + 1)) (hN f hf)
      rwa [map_pow, map_natCast] at this
  exact hT.1 (Fin d) (nmul c.μ p) E' hu hE' s

end GlobalTheory.EvP
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupDualTangentOfQuasiLogarithm

section

@[expose] public section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.QLogTangent

theorem smodEq_iff' {O : Type} [CommRing O] (p : O) (n : ℕ) (x y : O) :
    x ≡ y [SMOD (Ideal.span {p} ^ n • ⊤ : Submodule O O)] ↔ p ^ n ∣ x - y := by
  rw [SModEq.sub_mem, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, Ideal.mem_span_singleton]

theorem eq_zero_of_forall_dvd {O : Type} [CommRing O] (p : O) [IsHausdorff (Ideal.span {p}) O] (x : O)
    (h : ∀ n : ℕ, p ^ n ∣ x) : x = 0 :=
  IsHausdorff.haus' x fun n => (smodEq_iff' p n x 0).2 (by simpa using h n)

theorem main : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (E : Type) [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ f : MvPowerSeries (Fin d) E, QL c.μ ⊤ f → ∃! l : G.dual.Lie, c.IsLie f l := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv G d c E _ _ hF f hf
  have hinj : Function.Injective (algebraMap O E) := hF.inj
  have hlift : IsLift (RingHom.id O) c.μ :=
    ⟨c.isLaw.const, c.isLaw.unit, c.isLaw.comm, by simpa using c.isLaw⟩
  have hser : ∀ {τ : Type} (F : MvPowerSeries τ E), In (⊤ : Ideal O) F →
      ∃ s : MvPowerSeries τ O, map (algebraMap O E) s = F := by
    intro τ F hF'
    choose b _ hb using hF'
    let S : MvPowerSeries τ O := fun α => b α
    exact ⟨S, by ext α; rw [coeff_map, hb α]; rfl⟩
  have hminj : ∀ (s s' : MvPowerSeries (Fin d) O),
      map (algebraMap O E) s = map (algebraMap O E) s' → s = s' := by
    intro s s' h
    ext α
    apply hinj
    have := congrArg (coeff α) h
    simpa [coeff_map] using this
  have hdef : ∀ k, ∃ s : MvPowerSeries (Fin d) O, map (algebraMap O E) s = defect c.μ k f :=
    fun k => hser _ (GlobalTheory.QLogDefect.main p O O E (RingHom.id O) hF d c.μ hlift ⊤ f hf k).1
  obtain ⟨g, hg⟩ := hser _ hf.2.2
  choose s hs using hdef
  let a : ∀ n, G.A n := fun n => c.ev n (s (p ^ n))
  have hprim : ∀ n, ∃ t : G.A n ⊗[O] G.A n,
      Coalgebra.comul (R := O) (a n) = a n ⊗ₜ[O] (1 : G.A n) + (1 : G.A n) ⊗ₜ[O] a n + ((p : O) ^ n) • t := by
    intro n
    obtain ⟨h1, h2⟩ := GlobalTheory.CobDefect.main O E d c.μ c.isLaw hinj f g (s (p ^ n)) (p ^ n) hf.1 hg (hs _)
    refine ⟨c.ev₂ n g, ?_⟩
    show Coalgebra.comul (R := O) (c.ev n (s (p ^ n))) = _
    rw [GlobalTheory.QLog.Chart.comul_ev p C v O hv G d c n, h1, map_sub, map_smul, GlobalTheory.EvTor.ev₂_at_nmul_pow_self p C v O hv G d c n, h2, map_zero, sub_zero,
      Nat.cast_pow]
  have hcomp : ∀ n, ∃ b : G.A (n + 1), a (n + 1) = G.mulP n (a n) + ((p : O) ^ n) • b := by
    intro n
    have h := GlobalTheory.DefectComp.main O E d c.μ c.isLaw hinj f hf.1 (p ^ n) p (s (p ^ n)) (s p) (s (p ^ n * p))
      (hs _) (hs _) (hs _)
    refine ⟨c.ev (n + 1) (s p), ?_⟩
    show c.ev (n + 1) (s (p ^ (n + 1))) = G.mulP n (c.ev n (s (p ^ n))) + _
    rw [pow_succ, h, map_add (f := _), map_smul, GlobalTheory.EvP.ev_subst_nmul_p p C v O hv G d c n, Nat.cast_pow]
  have key : ∀ n (φ ψ : CartierDual O (G.A n)), PDiv.dUnit (R := O) φ = PDiv.dUnit (R := O) ψ →
      (p : O) ^ n ∣ φ (a n) - ψ (a n) := by
    intro n φ ψ h
    obtain ⟨t, ht⟩ := hprim n
    exact GlobalTheory.CotDualLin.dvd_sub_of_dUnit_eq O (G.A n) (a n) _ t ht φ ψ h
  have dsurj : ∀ n (x : PDiv.Cot O (CartierDual O (G.A n))), ∃ φ : CartierDual O (G.A n),
      PDiv.dUnit (R := O) φ = x := fun n x => AugCot.d_surjective _ x
  have haus : ∀ x : O, (∀ n : ℕ, (p : O) ^ n ∣ x) → x = 0 := eq_zero_of_forall_dvd (p : O)
  let Good : G.dual.omega → O → Prop := fun w L => ∀ n (φ : CartierDual O (G.A n)),
    PDiv.dUnit (R := O) φ = w.1 n → (p : O) ^ n ∣ L - φ (a n)
  have good_unique : ∀ w L L', Good w L → Good w L' → L = L' := by
    intro w L L' h h'
    refine sub_eq_zero.1 (haus _ fun n => ?_)
    obtain ⟨φ, hφ⟩ := dsurj n (w.1 n)
    have := dvd_sub (h n φ hφ) (h' n φ hφ)
    rwa [sub_sub_sub_cancel_right] at this
  have good_exists : ∀ w, ∃ L, Good w L := by
    intro w
    choose φ hφ using fun n => dsurj n (w.1 n)
    have step : ∀ n, (p : O) ^ n ∣ φ (n + 1) (a (n + 1)) - φ n (a n) := by
      intro n
      obtain ⟨b, hb⟩ := hcomp n
      have h1 : PDiv.dUnit (R := O) (CartierDual.map (G.mulP n) (φ (n + 1))) = w.1 n := by
        rw [← w.2 n, ← hφ (n + 1)]
        exact (PDiv.cotMap_d (G.dual.res n) (φ (n + 1))).symm
      have h2 := key n _ _ (h1.trans (hφ n).symm)
      rw [CartierDual.map_apply] at h2
      rw [hb, map_add (f := _), map_smul, smul_eq_mul]
      have e : φ (n + 1) (G.mulP n (a n)) + (p : O) ^ n * φ (n + 1) b - φ n (a n) =
          (φ (n + 1) (G.mulP n (a n)) - φ n (a n)) + (p : O) ^ n * φ (n + 1) b := by ring
      rw [e]
      exact dvd_add h2 (dvd_mul_right _ _)
    have cauchy : ∀ m n, m ≤ n → (p : O) ^ m ∣ φ n (a n) - φ m (a m) := by
      intro m n hmn
      induction n, hmn using Nat.le_induction with
      | base => simp
      | succ n hmn ih =>
        have := dvd_add ih ((pow_dvd_pow (p : O) hmn).trans (step n))
        rwa [add_comm, sub_add_sub_cancel] at this
    obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {(p : O)}) (fun n => φ n (a n))
      (fun {m n} hmn => (smodEq_iff' _ _ _ _).2 (dvd_sub_comm.1 (cauchy m n hmn)))
    refine ⟨L, fun n ψ hψ => ?_⟩
    have h1 := (smodEq_iff' _ _ _ _).1 (hL n)
    have h2 := key n _ _ ((hφ n).trans hψ.symm)
    have := dvd_add (dvd_sub_comm.1 h1) h2
    rwa [sub_add_sub_cancel] at this
  choose Lf hLf using good_exists
  have hgood_add : ∀ w w', Good (w + w') (Lf w + Lf w') := by
    intro w w' n φ hφ
    obtain ⟨φ1, h1⟩ := dsurj n (w.1 n)
    obtain ⟨φ2, h2⟩ := dsurj n (w'.1 n)
    have e : PDiv.dUnit (R := O) (φ1 + φ2) = PDiv.dUnit (R := O) φ := by
      have ea : PDiv.dUnit (R := O) (φ1 + φ2) = PDiv.dUnit (R := O) φ1 + PDiv.dUnit (R := O) φ2 := map_add (AugCot.d _) φ1 φ2
      rw [ea, h1, h2, hφ]; rfl
    have k := key n _ _ e
    have := dvd_add (dvd_add (hLf w n φ1 h1) (hLf w' n φ2 h2)) k
    have e2 : (φ1 + φ2) (a n) = φ1 (a n) + φ2 (a n) := rfl
    rw [e2] at this
    have e3 : Lf w - φ1 (a n) + (Lf w' - φ2 (a n)) + (φ1 (a n) + φ2 (a n) - φ (a n)) =
        Lf w + Lf w' - φ (a n) := by ring
    rwa [e3] at this
  have hgood_smul : ∀ (r : O) w, Good (r • w) (r * Lf w) := by
    intro r w n φ hφ
    obtain ⟨φ1, h1⟩ := dsurj n (w.1 n)
    have e : PDiv.dUnit (R := O) (r • φ1) = PDiv.dUnit (R := O) φ := by
      have ea : PDiv.dUnit (R := O) (r • φ1) = r • PDiv.dUnit (R := O) φ1 := map_smul (AugCot.d _) r φ1
      rw [ea, h1, hφ]; rfl
    have k := key n _ _ e
    have := dvd_add (dvd_mul_of_dvd_right (hLf w n φ1 h1) r) k
    have e2 : (r • φ1) (a n) = r * φ1 (a n) := rfl
    rw [e2] at this
    have e3 : r * (Lf w - φ1 (a n)) + (r * φ1 (a n) - φ (a n)) = r * Lf w - φ (a n) := by ring
    rwa [e3] at this
  let l : G.dual.Lie :=
    { toFun := Lf
      map_add' := fun w w' => good_unique _ _ _ (hLf (w + w')) (hgood_add w w')
      map_smul' := fun r w => good_unique _ _ _ (hLf (r • w)) (hgood_smul r w) }
  have hisLie : ∀ l' : G.dual.Lie, c.IsLie f l' ↔ ∀ w, Good w (l' w) := by
    intro l'
    constructor
    · intro h w n φ hφ
      exact h.2 n w φ (s (p ^ n)) hφ (hs _)
    · intro h
      refine ⟨fun n => In.top_iff.2 ⟨s (p ^ n), hs _⟩, fun n w φ s' hφ hs' => ?_⟩
      have : s' = s (p ^ n) := hminj _ _ (hs'.trans (hs _).symm)
      subst this
      exact h w n φ hφ
  refine ⟨l, (hisLie l).2 fun w => hLf w, fun l' hl' => ?_⟩
  exact LinearMap.ext fun w => good_unique _ _ _ ((hisLie l').1 hl' w) (hLf w)

end GlobalTheory.QLogTangent
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupDualTangentOfQuasiLogarithmStatement

section

@[expose] public section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.pDivGroup_dual_tangent_of_quasiLogarithm : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (E : Type) [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ f : MvPowerSeries (Fin d) E, QL c.μ ⊤ f → ∃! l : G.dual.Lie, c.IsLie f l := by
  first | exact @GlobalTheory.QLogTangent.main | exact GlobalTheory.QLogTangent.main | (intros; apply GlobalTheory.QLogTangent.main <;> assumption)
end
end
