module

public import Development.AbelianVarietyTheory.Definitions.Divisors.GhostFrobenius
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvEqOneOfForallPairing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOfIntegers
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTatePairingSandwich
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
public import Mathlib.RingTheory.Valuation.Integral
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivisibleGroupLatticeFreeRankHeightStatement
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InjectiveOfSmulMemRange
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.Linter.Style
import ReciprocityTheory.DualLattices.AinfFacts

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupExistsSmulMemSpanDlog

section

@[expose] public section

set_option autoImplicit false

open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.PDivLat

theorem lie_eq_zero_of_dlog {p : ℕ} [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O] (hv : v.Integers O)
    {ε : PreTilt O p} {hε : IsPrimitiveSystem ε} {G : PDivGroup p O} (hD : HasDatum hε G)
    (x : G.Lie) (hx : ∀ χ, x (dlog G χ) = 0) : x = 0 := by
  haveI : IsIntegrallyClosedIn O C := isIntegrallyClosedIn_iff.2 ⟨hv.hom_inj, fun h =>
    hv.exists_of_le_one (hv.isIntegral_iff_v_le_one.1 h)⟩
  obtain ⟨D, e, fil, lie, -, hb⟩ := hD
  have hG : Function.Surjective (G.pairing O).flip := (G.pairing_flip_bijective C).2
  have h0 : bQuot D (lie.symm x) = 0 :=
    GlobalTheory.DetInv.HTKer.pairingO_inj (hε := hε) hG e _ _ fun χ => by
      rw [hb, hx]; simp [pairingO]
  obtain ⟨m, hm⟩ := D.Fil.mkQ_surjective (lie.symm x)
  have h1 : D.bb m = 0 := by
    rw [← hm] at h0; exact h0
  have h2 : lie.symm x = 0 := by
    rw [← hm, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact h1
  simpa using congrArg lie h2

theorem exists_smul_mem_span_dlog : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ G : PDivGroup p O, HasDatum hε G → ∃ c : O, c ≠ 0 ∧ ∀ w : G.omega, c • w ∈ Submodule.span O (Set.range (dlog G)) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε G hD
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  haveI : Module.Finite O G.omega := (GlobalTheory.PDiv.omega_finite_projective p C v O hv G).1
  set S := Submodule.span O (Set.range (dlog G)) with hS
  let T := Submodule.torsion O (G.omega ⧸ S)
  let π : G.omega →ₗ[O] (G.omega ⧸ S) ⧸ T := T.mkQ ∘ₗ S.mkQ
  have hπ : Function.Surjective π := T.mkQ_surjective.comp S.mkQ_surjective
  haveI : Module.Flat O ((G.omega ⧸ S) ⧸ T) := by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout]
    exact Submodule.QuotientTorsion.torsion_eq_bot
  haveI : Module.Free O ((G.omega ⧸ S) ⧸ T) := Module.free_of_flat_of_isLocalRing
  let b := Module.Free.chooseBasis O ((G.omega ⧸ S) ⧸ T)
  have hcoord : ∀ i, b.coord i ∘ₗ π = 0 := fun i =>
    lie_eq_zero_of_dlog C hv hD _ fun χ => by
      change b.coord i (T.mkQ (S.mkQ (dlog G χ))) = 0
      have hs : S.mkQ (dlog G χ) = 0 := by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact Submodule.subset_span ⟨χ, rfl⟩
      rw [hs, map_zero, map_zero]
  have hzero : ∀ q : (G.omega ⧸ S) ⧸ T, q = 0 := fun q => by
    obtain ⟨w, rfl⟩ := hπ q
    refine b.ext_elem fun i => ?_
    change b.coord i (π w) = b.coord i 0
    rw [(b.coord i).map_zero]
    exact LinearMap.congr_fun (hcoord i) w
  have htor : Module.IsTorsion O (G.omega ⧸ S) := fun q => by
    have := hzero (T.mkQ q)
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_torsion_iff] at this
    exact this
  obtain ⟨c, hc, hc0⟩ := Submodule.annihilator_top_inter_nonZeroDivisors htor
  refine ⟨c, nonZeroDivisors.ne_zero hc0, fun w => ?_⟩
  have := Submodule.mem_annihilator.1 hc (S.mkQ w) Submodule.mem_top
  rwa [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this

end GlobalTheory.PDivLat
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupExistsSmulMemSpanDlogStatement

section

@[expose] public section

open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.pDivGroup_exists_smul_mem_span_dlog : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ G : PDivGroup p O, HasDatum hε G → ∃ c : O, c ≠ 0 ∧ ∀ w : G.omega, c • w ∈ Submodule.span O (Set.range (dlog G)) := by
  first | exact @GlobalTheory.PDivLat.exists_smul_mem_span_dlog | exact GlobalTheory.PDivLat.exists_smul_mem_span_dlog | (intros; apply GlobalTheory.PDivLat.exists_smul_mem_span_dlog <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupHodgeTateFirstMapNatural

section

@[expose] public section

open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.PDivLat.HodgeNat

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O]

theorem theta_xi_eq_zero [IsDomain O] {ε : PreTilt O p} (hε : IsPrimitiveSystem ε) :
    WittVector.fontaineTheta O p (xi ε) = 0 := by
  have h1 : IsPrimitiveRoot (zeta ε 1) p := by simpa using hε 1
  have h2 := h1.geom_sum_eq_zero (Fact.out : p.Prime).one_lt

  rw [xi, map_sum]
  simpa [map_pow, WittVector.fontaineTheta_teichmuller, zeta] using h2

theorem ghost_mu_eq_zero [IsDomain O] {ε : PreTilt O p} (hε : IsPrimitiveSystem ε) (n : ℕ) :
    ghost p O n (Sandwich.mu ε) = 0 := by
  induction n with
  | zero =>
    show WittVector.fontaineTheta O p (Sandwich.mu ε) = 0
    rw [Sandwich.mu, map_sub, WittVector.fontaineTheta_teichmuller, map_one, sub_eq_zero]
    exact hε.zeta_zero
  | succ n ih =>
    rw [← ghost_frobenius, Dieudonne.frobenius_mu, ghost_mul, ih, mul_zero]

noncomputable def muPair [IsDomain O] {ε : PreTilt O p} (hε : IsPrimitiveSystem ε) (G : PDivGroup p O)
    (χ : G.dual.Tate) : TDual G where
  toFun t := Sandwich.mu ε * ofPadic p O (epsPairing hε G t χ)
  map_add' s t := by
    simp only [epsPairing, map_add (f := _), LinearMap.add_apply, mul_add]
  map_smul' a t := by
    simp only [epsPairing, map_smul, LinearMap.smul_apply, smul_eq_mul, map_mul]
    ring

theorem muPair_mem [IsDomain O] {ε : PreTilt O p} (hε : IsPrimitiveSystem ε) (G : PDivGroup p O)
    (χ : G.dual.Tate) : muPair hε G χ ∈ latt G := fun n =>
  ⟨0, fun t => by
    show ghost p O n (Sandwich.mu ε * ofPadic p O (epsPairing hε G t χ)) = 0
    rw [ghost_mul, ghost_mu_eq_zero hε, zero_mul]⟩

end GlobalTheory.PDivLat.HodgeNat


open GlobalTheory.PDivLat.HodgeNat in
theorem GlobalTheory.PDivLat.iota_natural : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ (G H : PDivGroup p O) (f : G ⟶ H), HasDatum hε G → HasDatum hε H → ∀ (M : Type) [AddCommGroup M] [Module O M] (r : latt G →ₛₗ[WittVector.fontaineTheta O p] M) (M' : Type) [AddCommGroup M'] [Module O M'] (r' : latt H →ₛₗ[WittVector.fontaineTheta O p] M') (u : M' →ₗ[O] M) (ι : G.omega →ₗ[O] M) (ι' : H.omega →ₗ[O] M'), Function.Surjective r → (∀ m, r m = 0 ↔ ∃ n, m = xi ε • n) → (∀ y, u (r' y) = r (lattMap f y)) → (∀ (χ : G.dual.Tate) (y : latt G), (∀ t, y.1 t = Sandwich.mu ε * ofPadic p O (epsPairing hε G t χ)) → ι (dlog G χ) = r y) → (∀ (χ : H.dual.Tate) (y : latt H), (∀ t, y.1 t = Sandwich.mu ε * ofPadic p O (epsPairing hε H t χ)) → ι' (dlog H χ) = r' y) → ∀ w, u (ι' w) = ι (omegaMap G H f w) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε G H f hG hH M _ _ r M' _ _ r' u ι ι' hrs hrk hu hι hι' w
  obtain ⟨hfree, hfin, -⟩ := GlobalTheory.T.pDivisibleGroup_lattice_free_rank_height p C v O hv ε hε G hG
  haveI : Nontrivial (Ainf p O) := (ReciprocityTheory.PGsh.Ainf.theta_surj p O hv).nontrivial
  obtain ⟨hMfree, -, -⟩ := Dieudonne.free_of_reduction (ReciprocityTheory.PGsh.Ainf.theta_surj p O hv)
    (theta_xi_eq_zero hε) r hrs fun m hm => (hrk m).1 hm
  haveI := hMfree

  have key : ∀ χ : H.dual.Tate, u (ι' (dlog H χ)) = ι (omegaMap G H f (dlog H χ)) := by
    intro χ
    let Y : latt H := ⟨muPair hε H χ, muPair_mem hε H χ⟩
    have h1 : ι' (dlog H χ) = r' Y := hι' χ Y fun t => rfl
    have h2 : ι (dlog G (tateMap H.dual G.dual O (dualHom G H f) χ)) = r (lattMap f Y) := by
      refine hι _ _ fun t => ?_
      show Sandwich.mu ε * ofPadic p O (epsPairing hε H (tateMap G H O f t) χ) = _
      rw [epsPairing, epsPairing, pairing_tateMap]
    rw [h1, hu, ← h2, dlog_tateMap]
  obtain ⟨c, hc, hcw⟩ := GlobalTheory.T.pDivGroup_exists_smul_mem_span_dlog p C v O hv ε hε H hH
  have hspan : ∀ x ∈ Submodule.span O (Set.range (dlog H)),
      u (ι' x) = ι (omegaMap G H f x) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨χ, rfl⟩ := hx; exact key χ
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul a x _ hx => simp [hx]
  have h := hspan _ (hcw w)
  simp only [map_smul] at h
  have h' : c • (u (ι' w) - ι (omegaMap G H f w)) = 0 := by rw [smul_sub, h, sub_self]
  have tf : ∀ x : M, c • x = 0 → x = 0 := by
    intro x hx
    let b := Module.Free.chooseBasis O M
    refine b.repr.injective (Finsupp.ext fun i => ?_)
    have h3 := congrArg (fun y => b.repr y i) hx
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_zero, Finsupp.coe_zero, Pi.zero_apply] at h3
    simpa using (mul_eq_zero.1 h3).resolve_left hc
  exact sub_eq_zero.1 (tf _ h')
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupHodgeTateFirstMapNaturalStatement

section

@[expose] public section

open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.pDivGroup_hodgeTateFirstMap_natural : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ (G H : PDivGroup p O) (f : G ⟶ H), HasDatum hε G → HasDatum hε H → ∀ (M : Type) [AddCommGroup M] [Module O M] (r : latt G →ₛₗ[WittVector.fontaineTheta O p] M) (M' : Type) [AddCommGroup M'] [Module O M'] (r' : latt H →ₛₗ[WittVector.fontaineTheta O p] M') (u : M' →ₗ[O] M) (ι : G.omega →ₗ[O] M) (ι' : H.omega →ₗ[O] M'), Function.Surjective r → (∀ m, r m = 0 ↔ ∃ n, m = xi ε • n) → (∀ y, u (r' y) = r (lattMap f y)) → (∀ (χ : G.dual.Tate) (y : latt G), (∀ t, y.1 t = Sandwich.mu ε * ofPadic p O (epsPairing hε G t χ)) → ι (dlog G χ) = r y) → (∀ (χ : H.dual.Tate) (y : latt H), (∀ t, y.1 t = Sandwich.mu ε * ofPadic p O (epsPairing hε H t χ)) → ι' (dlog H χ) = r' y) → ∀ w, u (ι' w) = ι (omegaMap G H f w) := by
  first | exact @GlobalTheory.PDivLat.iota_natural | exact GlobalTheory.PDivLat.iota_natural | (intros; apply GlobalTheory.PDivLat.iota_natural <;> assumption)
end
end
