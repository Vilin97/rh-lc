module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColRecCEvBijective
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Formalism.LocalToGlobal.Columns.GoodXgE
public import Formalism.LocalToGlobal.Columns.RecPerFF
public import Formalism.LocalToGlobal.KernelLattices.JetFieldLeKR
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsAbsIrrCharCompIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EvaluationDatumOkBaseTuple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrdSubDetSubStdL
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NuRowSuccEqWt
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.LocalToGlobal.Columns.BaseLemmas
public import Formalism.LocalToGlobal.Columns.InvariantSubspaceCoordsX
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ColInst
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceModelImp
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
public import Formalism.LocalToGlobal.Divisibility.MemberDIV

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSelfDualLatticeNormOneIdealRankOne

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.L2.Indef GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.R3
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.R3.SelC

theorem mem_iff_trace {K G : Type} [Field K] [CharZero K] [Group G] [Fintype G] (Xg : Finset (G → K))
    (hXg : ∀ χ ∈ Xg, IsAbsIrrChar χ) {χ : G → K} (hχ : IsAbsIrrChar χ) :
    χ ∈ Xg ↔ ∑ g, (idemOf Xg).coeff g * χ g = χ 1 := by
  classical
  have hN : ((Fintype.card G : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have h1 : χ 1 ≠ 0 := by
    intro h0
    have h := conv_char hχ hχ
    obtain ⟨n, ρ, hi, hρ⟩ := hχ
    have e := hρ 1
    rw [h0, map_zero, Representation.char_one, Module.finrank_fin_fun, Nat.cast_eq_zero] at e
    subst e
    exact (bot_ne_top (α := Subrepresentation ρ)) (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))
  have hterm : ∀ ψ ∈ Xg, ∑ g, (chiIdem ψ).coeff g * χ g = if ψ = χ then χ 1 else 0 := by
    intro ψ hψ
    have h := conv_char (hXg ψ hψ) hχ 1
    simp only [mul_one] at h
    have e : ∑ g, (chiIdem ψ).coeff g * χ g = ψ 1 / (Fintype.card G : K) * ∑ g, ψ g⁻¹ * χ g := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun g _ => by rw [coeff_chiIdem, mul_assoc]
    rw [e]
    split_ifs at h ⊢ with hc
    · rw [mul_right_cancel₀ h1 h, hc]
      field_simp
    · rw [(mul_eq_zero.1 h).resolve_right h1, mul_zero]
  have hsum : ∑ g, (idemOf Xg).coeff g * χ g = if χ ∈ Xg then χ 1 else 0 := by
    unfold idemOf
    simp only [MonoidAlgebra.coeff_sum, Finset.sum_apply', Finset.sum_mul]
    rw [Finset.sum_comm, Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
  rw [hsum]
  split_ifs with hc
  · exact iff_of_true hc rfl
  · exact iff_of_false hc h1.symm

theorem mem_iff_XgE {K G H : Type} [Field K] [CharZero K] [Group G] [Fintype G] [Group H] [Fintype H] (σ : K →+* ℂ) (eG : G ≃* H)
    (e : MonoidAlgebra ℂ H) (Xg : Finset (G → K)) (hXg : ∀ χ ∈ Xg, IsAbsIrrChar χ)
    (he : ∀ g, σ ((idemOf Xg).coeff g) = e.coeff (eG g)) (χ : G → K) :
    χ ∈ Xg ↔ (fun g => χ (eG.symm g)) ∈ XgE σ e := by
  rw [mem_XgE, isAbsIrrChar_comp_iff eG.symm, ← Equiv.sum_comp eG.toEquiv]

  simp only [MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe, MulEquiv.symm_apply_apply, map_one, ← he, ← map_mul, ← map_sum]
  rw [σ.injective.eq_iff]
  exact ⟨fun h => ⟨hXg χ h, (mem_iff_trace Xg hXg (hXg χ h)).1 h⟩, fun h => (mem_iff_trace Xg hXg h.1).2 h.2⟩

theorem exists_coord {K W : Type} [Field K] [AddCommGroup W] [Module ℂ W] (σ : K →+* ℂ) {n d : ℕ}
    (Ψ : (Fin n → K) ≃ₗ[K] (Fin d → K)) (j : (Fin n → K) →ₛₗ[σ] W)
    (li : LinearIndependent ℂ fun i => j (Pi.single i 1)) (sp : Submodule.span ℂ (Set.range fun i => j (Pi.single i 1)) = ⊤) :
    ∃ ι : W ≃ₗ[ℂ] (Fin d → ℂ), ∀ y, ι (j y) = fun a => σ (Ψ y a) := by
  classical
  let b : Module.Basis (Fin n) ℂ W := Module.Basis.mk li sp.ge
  have hb : ∀ y, b.equivFun (j y) = fun i => σ (y i) := by
    intro y
    rw [← LinearEquiv.eq_symm_apply, Module.Basis.equivFun_symm_apply]
    conv_lhs => rw [pi_eq_sum_univ' y]

    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.map_smulₛₗ, Module.Basis.mk_apply]
  let A := LinearMap.toMatrix' Ψ.toLinearMap
  let A' := LinearMap.toMatrix' Ψ.symm.toLinearMap
  have h1 : A * A' = 1 := by
    rw [← LinearMap.toMatrix'_comp]
    simp
  have h2 : A' * A = 1 := by
    rw [← LinearMap.toMatrix'_comp]
    simp
  let E : (Fin n → ℂ) ≃ₗ[ℂ] (Fin d → ℂ) := LinearEquiv.ofLinear (Matrix.toLin' (A.map σ)) (Matrix.toLin' (A'.map σ))
    (by rw [← Matrix.toLin'_mul, ← Matrix.map_mul, h1]; simp) (by rw [← Matrix.toLin'_mul, ← Matrix.map_mul, h2]; simp)
  refine ⟨b.equivFun.trans E, fun y => ?_⟩
  rw [LinearEquiv.trans_apply, hb]
  funext a
  show (A.map σ).mulVec (σ ∘ y) a = _
  rw [← RingHom.map_mulVec]
  exact congrArg σ (congrFun (LinearMap.toMatrix'_mulVec Ψ.toLinearMap y) a)

section Rows

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)

theorem rowCast_lin {SG' : Finset (HeightOneSpectrum (𝓞 X.E))} (e : Pr.vGs = SG') (A : LevFam X.E X.K (R.N R.m - 1) Pr.vGs)
    (Λ' : LevFam X.E X.K (R.N R.m - 1) SG') (hΛ : Λ' = e ▸ A) :
    ((formGSD (rowVal W SG') Λ').Ok → (rowGSD W A).Ok) ∧
      ∃ L : (formGSD (rowVal W SG') Λ').EqFun ≃ₗ[X.K] (rowGSD W A).EqFun, ∀ F, L F = rowCast W e A Λ' hΛ F := by
  subst hΛ
  subst e
  exact ⟨id, LinearEquiv.refl _ _, fun _ => rfl⟩

variable (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (hX : X.Ok) (P : LevFam X.E X.K R.r Pr.vGs)


include hX in
theorem rowG_ok (hQ : QE sel (mu : Chr X.F X.E X.K) = ∅) : (rowGSD W (rowTyG Ch P).inv).Ok :=
  (rowCast_lin W (rcol_rowSG_eq sel mu hQ) (rowTyG Ch P).inv _ (rowTy_inv_cast Ch sel mu hQ P)).1 (mtildeOk W Ch sel mu hX P)

theorem exists_lvlEquiv : ∃ Φ : (Fin ((MtildeKCSD W Ch sel mu (mtildeKOk W Ch sel mu hX)).lvlDim
      (g0Act W Ch sel mu (mtildeKOk W Ch sel mu hX)) P.grp P.chr) → X.K) ≃ₗ[X.K] MtildeV W Ch sel mu P,
    ∀ y, ∃ hK : (Φ y).1 ∈ (mtildeKGSD W Ch sel mu).EqFun,
      (mtildeKGSD W Ch sel mu).res (mtildeKOk W Ch sel mu hX) ⟨(Φ y).1, hK⟩ =
        (MtildeKCSD W Ch sel mu (mtildeKOk W Ch sel mu hX)).basis.equivFun.symm
          (((MtildeKCSD W Ch sel mu (mtildeKOk W Ch sel mu hX)).lvlE (g0Act W Ch sel mu (mtildeKOk W Ch sel mu hX)) P.grp P.chr).mulVec y) := by
  set h := mtildeKOk W Ch sel mu hX
  have hr : LinearMap.range ((MtildeKCSD W Ch sel mu h).lvlE (g0Act W Ch sel mu h) P.grp P.chr).mulVecLin =
      (MtildeKCSD W Ch sel mu h).lvlPart (g0Act W Ch sel mu h) P.grp P.chr :=
    (image_idempotent_spec X.K _ _).2.trans (level_part_spec X.K _ _ _ _ _)
  let c := (mtildeKGSD W Ch sel mu).coordOf h (mtildeKGSD W Ch sel mu).outSec
  let f0 := c.symm.toLinearMap ∘ₗ ((MtildeKCSD W Ch sel mu h).lvlE (g0Act W Ch sel mu h) P.grp P.chr).mulVecLin
  have hf0 : ∀ y, c (f0 y) = ((MtildeKCSD W Ch sel mu h).lvlE (g0Act W Ch sel mu h) P.grp P.chr).mulVec y :=
    fun y => c.apply_symm_apply _
  have hm : ∀ y, ((mtildeKGSD W Ch sel mu).EqFun.subtype ∘ₗ f0) y ∈ (mtildeGSD W Ch sel mu P).EqFun := fun y => by
    refine (mem_lvlPartX_iff W Ch sel mu P h (f0 y)).1 ?_
    rw [← hr]
    exact ⟨y, (hf0 y).symm⟩
  let f := LinearMap.codRestrict _ _ hm
  have hinj : Function.Injective f := fun y y' e => by
    have e1 : f0 y = f0 y' := Subtype.ext (congrArg Subtype.val e :)
    exact (image_idempotent_spec X.K _ _).1 ((hf0 y).symm.trans ((congrArg c e1).trans (hf0 y')))
  have hsurj : Function.Surjective f := fun x => by
    obtain ⟨hK, -⟩ := (mem_MtildeV_iff W Ch sel mu P x.1).1 x.2
    have h1 := (mem_lvlPartX_iff W Ch sel mu P h ⟨x.1, hK⟩).2 x.2
    rw [← hr] at h1
    obtain ⟨y, hy⟩ := h1
    have e1 : f0 y = ⟨x.1, hK⟩ := c.injective ((hf0 y).trans hy)
    exact ⟨y, Subtype.ext (congrArg Subtype.val e1 :)⟩
  refine ⟨LinearEquiv.ofBijective f ⟨hinj, hsurj⟩, fun y => ⟨(f0 y).2, ?_⟩⟩
  rw [← hf0]
  exact (LinearEquiv.symm_apply_apply _ _).symm

theorem exists_read (hQ : QE sel (mu : Chr X.F X.E X.K) = ∅) (σ : X.K →+* ℂ) (hM : (rowGSD W (rowTyG Ch P).inv).Ok)
    {V : Type} [AddCommGroup V] [Module ℂ V]
    (j : (Fin ((MtildeKCSD W Ch sel mu (mtildeKOk W Ch sel mu hX)).lvlDim
      (g0Act W Ch sel mu (mtildeKOk W Ch sel mu hX)) P.grp P.chr) → X.K) →ₛₗ[σ] V)
    (li : LinearIndependent ℂ fun i => j (Pi.single i 1)) (sp : Submodule.span ℂ (Set.range fun i => j (Pi.single i 1)) = ⊤) :
    ∃ ι : V ≃ₗ[ℂ] (Fin ((rowGSD W (rowTyG Ch P).inv).hDim hM) → ℂ), ∀ y,
      ∃ (F' : (mtildeKGSD W Ch sel mu).EqFun) (hm : F'.1 ∈ (mtildeGSD W Ch sel mu P).EqFun),
        (mtildeKGSD W Ch sel mu).res (mtildeKOk W Ch sel mu hX) F' =
          (MtildeKCSD W Ch sel mu (mtildeKOk W Ch sel mu hX)).basis.equivFun.symm
            (((MtildeKCSD W Ch sel mu (mtildeKOk W Ch sel mu hX)).lvlE (g0Act W Ch sel mu (mtildeKOk W Ch sel mu hX)) P.grp P.chr).mulVec y) ∧
        ι (j y) = zOfRow W Ch sel mu hQ P σ hM ⟨F'.1, hm⟩ := by
  obtain ⟨Φ, hΦ⟩ := exists_lvlEquiv W Ch sel mu hX P
  obtain ⟨L, hL⟩ := (rowCast_lin W (rcol_rowSG_eq sel mu hQ) (rowTyG Ch P).inv _ (rowTy_inv_cast Ch sel mu hQ P)).2
  obtain ⟨ι, hι⟩ := exists_coord σ ((Φ.trans L).trans ((rowGSD W (rowTyG Ch P).inv).hB hM).equivFun) j li sp
  refine ⟨ι, fun y => ?_⟩
  obtain ⟨hK, e⟩ := hΦ y
  refine ⟨⟨(Φ y).1, hK⟩, (Φ y).2, e, (hι y).trans ?_⟩
  unfold zOfRow zOfRow0
  rw [← hL]
  rfl

end Rows

section Weights

variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l))

theorem nuT_eq (u : B.Word) {i : ℕ} (hi : i < B.R.m) (τ : Tau B.R) (r : Fin (B.R.N i)) :
    ((nuT (I.rec7 l Z) u i τ r : ℕ) : ℤ) = (B.wts.nuW u (i + 1) τ).w r := by
  have e1 : ((nuT (I.rec7 l Z) u i τ r : ℕ) : ℝ) = DV.nuRow (I.rec7 l Z) u (i + 1) τ r := (nu_t_identity (I.rec7 l Z) u i hi τ r).1
  have e2 := GlobalTheory.ColPeriod.nuRow_succ_eq_wt (I.rec7 l Z) u i hi τ r r.2
  have e3 := B.wts.nuW_eq u hi τ r
  have e4 := lamOf_wtN (B.wts.hc u τ) hi.le r
  have key : (((nuT (I.rec7 l Z) u i τ r : ℕ) : ℤ) : ℝ) = (((B.wts.nuW u (i + 1) τ).w r : ℤ) : ℝ) := by
    rw [Int.cast_natCast, e1, e2, ← Rat.cast_intCast, e3]
    unfold Wts.lamN at e3 ⊢
    rw [e4]
    rfl
  exact_mod_cast key

theorem wtTie_base {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : G.Inst (I.rec7 l Z) L} {Gl : G.LatInst (I.rec7 l Z)}
    {K : G.Consts} {Y : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX} (t : KerEntTied ex) :
    t.WtTie (fun u i τ => B.wts.lamTrue u i τ) (fun u i τ => (B.wts.lamTrue u i τ).detShift)
      (fun u i τ => nuLast (Pr := B.primes X) B.wts u i τ) := by
  intro (u : B.Word) μ i hi
  have hi' : i < B.R.m := hi
  have hN : 0 < B.R.N i := B.R.N_pos i
  have hN' : 0 < B.R.N (i + 1) := B.R.N_pos (i + 1)
  have hlt : B.R.N i < B.R.N (i + 1) := by unfold Ranks.N; rw [Nat.succ_mul]; omega
  have d0 : ∀ τ, (B.wts.lamTrue u i τ).detShift = (B.wts.lamTrue u i τ).w ⟨B.R.N i - 1, by omega⟩ := fun τ => dif_pos hN
  have d' : ∀ τ, (B.wts.lamTrue u (i + 1) τ).detShift = (B.wts.lamTrue u (i + 1) τ).w ⟨B.R.N (i + 1) - 1, by omega⟩ :=
    fun τ => dif_pos hN'
  have dn : ∀ τ, (B.wts.nuW u (i + 1) τ).detShift = (B.wts.nuW u (i + 1) τ).w (⟨B.R.N i - 1, by omega⟩ : Fin (B.R.N i)) :=
    fun τ => dif_pos hN
  have hs : ∀ (τ : Tau B.R) (r : Fin (B.R.N i)),
      (B.wts.nuW u (i + 1) τ).w r = (B.wts.lamTrue u i τ).w r + ((I.rec7 l Z).chTw u μ).sSharp i τ := fun τ r => by
    have e1 := B.wts.nuW_eq_true u hi' τ r
    have e2 : ((((I.rec7 l Z).chTw u μ).sSharp i τ : ℤ) : ℚ) = sExp' B.R ((B.wts.hc u τ).e ⟨i, hi'⟩) (i + 1) :=
      ((I.rec7 l Z).chTw u μ).sSharp_eq i hi τ
    rw [← e2] at e1
    exact_mod_cast e1
  have hl : ∀ τ, ((nuLast (Pr := B.primes X) B.wts u i τ : ℕ) : ℤ) =
      (B.wts.lamTrue u i τ).detShift + ((I.rec7 l Z).chTw u μ).sSharp i τ := fun τ => by
    rw [nuLast_eq (Pr := B.primes X) B.wts u i hi' τ, dn, hs, d0]
  refine ⟨fun (τ : Tau B.R) (r : Fin (B.R.N i)) => ?_, fun τ => (hl τ).symm, fun (τ : Tau B.R) => ?_, jet_in_weight_space_chain (Pr := B.primes X) B.wts u hi'⟩
  · have e1 := nuT_eq I l Z u hi' τ r
    have e2 := hs τ r
    have e3 := hl τ
    have hanti : (B.wts.lamTrue u i τ).detShift ≤ (B.wts.lamTrue u i τ).w r := by
      refine (d0 τ).trans_le ?_
      exact (B.wts.lamTrue u i τ).anti (by show r.1 ≤ B.R.N i - 1; have : r.1 < B.R.N i := r.2; omega)
    show ((B.wts.lamTrue u i τ).w r - (B.wts.lamTrue u i τ).detShift).toNat + nuLast (Pr := B.primes X) B.wts u i τ = nuT (I.rec7 l Z) u i τ r
    omega
  · have e1 := B.wts.lamTrue_new u hi' τ ⟨B.R.N (i + 1) - 1, by omega⟩ (by show ¬ B.R.N (i + 1) - 1 < B.R.N i; omega)
    have e2 : ((((I.rec7 l Z).chTw u μ).sDiv i τ : ℤ) : ℚ) = sExp B.R ((B.wts.hc u τ).e ⟨i, hi'⟩) (i + 1) :=
      ((I.rec7 l Z).chTw u μ).sDiv_eq i hi τ
    rw [← e2] at e1
    refine (d' τ).trans ?_
    exact_mod_cast e1

end Weights

section Chi

variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l))

theorem isSelfDualLattice_normOne_ideal_rankOne {D : D7} {𝔞 : TaylorLogMetric.IdE D} (h : TaylorLogMetric.N1 D 𝔞) :
    IsSDLat D.host.E 1 (Submodule.pi Set.univ fun _ : Fin 1 => 𝔞) := by
  obtain ⟨𝔟, hb, hab⟩ := h
  have hc : ∀ x : D.host.E, star x = D.host.conj x := fun x => bridge_star_holds D.R D.host x
  have hfg : 𝔞.FG := Submodule.fg_of_isUnit (IsUnit.of_mul_eq_one 𝔟 hab)
  refine ⟨Submodule.fg_pi fun _ => hfg, ?_, fun y => ?_⟩
  · obtain ⟨x, hx, h0⟩ : ∃ x ∈ 𝔞, x ≠ 0 := by
      by_contra hn
      push Not at hn
      have : 𝔞 = ⊥ := (Submodule.eq_bot_iff _).2 hn
      rw [this, Submodule.bot_mul] at hab
      have h1 : (1 : D.host.E) ∈ (1 : TaylorLogMetric.IdE D) := Submodule.one_le.1 le_rfl
      rw [← hab] at h1
      exact one_ne_zero ((Submodule.mem_bot _).1 h1)
    rw [eq_top_iff]
    intro v _
    have : v = (v 0 / x) • (fun _ : Fin 1 => x) := by
      funext i
      rw [Subsingleton.elim i 0]
      simp [h0]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span fun _ _ => hx)
  · constructor
    · intro hy x hx
      have h1 : y 0 * star (x 0) ∈ 𝔞 * 𝔟 := Submodule.mul_mem_mul (hy 0 trivial) ((hb _).2 (by rw [← hc, star_star]; exact hx 0 trivial))
      rw [hab, Submodule.mem_one] at h1
      obtain ⟨r, hr⟩ := h1
      exact ⟨r, by rw [hr]; simp [stdH, mul_comm]⟩
    · intro hy i _
      rw [Subsingleton.elim i 0]
      have h1 : Submodule.span (𝓞 D.host.E) {y 0} * 𝔟 ≤ 1 := by
        rw [Submodule.span_singleton_mul]
        intro z hz
        obtain ⟨b, hb', rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hz
        obtain ⟨r, hr⟩ := hy (fun _ => star b) fun _ _ => by rw [hc]; exact (hb b).1 hb'
        exact Submodule.mem_one.2 ⟨r, by rw [hr]; simp [stdH, mul_comm]⟩
      have h2 : Submodule.span (𝓞 D.host.E) {y 0} ≤ 𝔞 := by
        calc Submodule.span (𝓞 D.host.E) {y 0} = 𝔞 * (Submodule.span (𝓞 D.host.E) {y 0} * 𝔟) := by
              rw [mul_left_comm, hab, mul_one]
          _ ≤ 𝔞 * 1 := mul_le_mul_right h1 𝔞
          _ = 𝔞 := mul_one _
      exact h2 (Submodule.mem_span_singleton_self _)

theorem detId_rank_one {R : Ranks} (H : Host R) (𝔞 : Submodule (𝓞 H.E) H.E) :
    Th.detId H (Th.stdL H 1) (Submodule.pi Set.univ fun _ : Fin 1 => 𝔞) = 𝔞 := by
  rw [GlobalTheory.Mem.ChiDet.detId_stdL]
  unfold GlobalTheory.Mem.Chr.detSub
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    rw [Matrix.det_unique]
    exact hx _ _ trivial
  · intro a ha
    exact Submodule.subset_span ⟨fun _ _ => a, fun _ _ _ => ha, by rw [Matrix.det_unique]; rfl⟩

theorem chiRec_eq_chi {idl : (I.rec7 l Z).Dt ⧸ (I.rec7 l Z).UO → TaylorLogMetric.IdE (I.rec7 l Z)} (hidl : TaylorLogMetric.RelDetPinned (I.rec7 l Z) idl)
    (𝔞 : TaylorLogMetric.IdE (I.rec7 l Z)) (h : TaylorLogMetric.N1 (I.rec7 l Z) 𝔞) : TaylorLogMetric.chiRec (I.rec7 l Z) idl 𝔞 = I.chi 𝔞 := by
  have h1 : TaylorLogMetric.N1 (I.rec7 l Z) 1 := by
    have := RcHyp.n1_span_unitary (D := I.rec7 l Z) 1
    rwa [OneMemClass.coe_one, ← Submodule.one_eq_span] at this
  have hs := isSelfDualLattice_normOne_ideal_rankOne h
  have h2 := hidl.2.2.2.2 1 ⟨_, isSelfDualLattice_normOne_ideal_rankOne h1⟩ ⟨_, hs⟩
  have h3 : TaylorLogMetric.detId (I.rec7 l Z) (Submodule.pi Set.univ fun _ : Fin 1 => (1 : TaylorLogMetric.IdE (I.rec7 l Z)))
      (Submodule.pi Set.univ fun _ : Fin 1 => 𝔞) = 𝔞 := detId_rank_one B.host 𝔞
  have h4 := h2.trans h3
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (relDetQ B.host I.SQ 1 (Th.stdL B.host 1) (Submodule.pi Set.univ fun _ : Fin 1 => 𝔞))
  have h5 : idl (QuotientGroup.mk x) = 𝔞 := (congrArg idl hx).trans h4
  have h6 := GlobalTheory.Mem.ChiDet.tildeD_eq_chiId B.R B.host I.C.chiPsi I.C.isChi 1 (Submodule.pi Set.univ fun _ : Fin 1 => 𝔞) (Submodule.IsLattice.of_fg B.host.E hs.1)
    (toDtT B.host I.SQ x) (congrArg (toDtTMod B.host I.SQ) hx)
  replace h6 := h6.trans (congrArg (chiId I.C.chiPsi) (detId_rank_one B.host 𝔞))
  refine ((congrArg _ h5.symm).trans (TaylorLogMetric.chiRec_idl _ _ hidl.1 _)).trans (Eq.trans ?_ h6)
  show ((tildeQ B.host I.SQ I.C.chiPsi x : ℂˣ) : ℂ) = _
  rw [tildeQ_eq_comp B.host I.SQ (KD_le_ker_of_isChiPsi I.C.isChi)]
  rfl

theorem ker_chi_eq {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : G.Inst (I.rec7 l Z) L} {Gl : G.LatInst (I.rec7 l Z)}
    {K : G.Consts} {Y : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX} (t : KerEntTied ex) :
    ∀ 𝔞, TaylorLogMetric.N1 (I.rec7 l Z) 𝔞 → t.χ 𝔞 = I.chi 𝔞 := fun 𝔞 h => by
  rw [t.χ_rec]
  exact chiRec_eq_chi I l Z t.idl_ok 𝔞 h

end Chi

end GlobalTheory.Mem.R3.SelC

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRowsOfHeqData

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.L2.Indef GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.R3
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.R3.SelC

theorem exists_moved {K T : Type} [Field K] {σ : K →+* ℂ} {n : ℕ} {A : T → Type} [∀ t, AddCommGroup (A t)] [∀ t, Module ℂ (A t)]
    {V : Type} [AddCommGroup V] [Module ℂ V] {a b : T} (h : a = b) (E : V ≃ₗ[ℂ] A b) (j : (Fin n → K) →ₛₗ[σ] A a)
    (li : LinearIndependent ℂ fun i => j (Pi.single i 1)) (sp : Submodule.span ℂ (Set.range fun i => j (Pi.single i 1)) = ⊤) :
    ∃ j' : (Fin n → K) →ₛₗ[σ] V, (∀ y, j' y = E.symm (h ▸ j y)) ∧ (LinearIndependent ℂ fun i => j' (Pi.single i 1)) ∧
      Submodule.span ℂ (Set.range fun i => j' (Pi.single i 1)) = ⊤ := by
  subst h
  refine ⟨E.symm.toLinearMap.comp j, fun _ => rfl, li.map' E.symm.toLinearMap E.symm.ker, ?_⟩
  have := congrArg (Submodule.map E.symm.toLinearMap) sp
  rwa [Submodule.map_span, ← Set.range_comp, Submodule.map_top, LinearEquiv.range] at this

section Gen

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (hX : X.Ok)
  (v0 : InfinitePlace X.K) (TU : Finset (Tup X.F X.E X.K S))
  (Xg : Finset (Formalism.L2.Col.G0 X.E Pr.vGs R.r → X.K)) (S0 : Set (HeightOneSpectrum (𝓞 X.E)))
  (xiVal : Tup X.F X.E X.K S → HeightOneSpectrum (𝓞 X.E) → X.Kˣ)
  (trIv : Fin R.m → (LevOffI ∅ Pr.vGs S0 × List ℕ → X.K) → LevOffI ∅ Pr.vGs S0 × List ℕ → X.K)
  (P : LevFam X.E X.K R.r Pr.vGs)

theorem exists_read_fam {s : ℕ} (hOk : (colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.Ok s)
    (σ : X.K →+* ℂ) (hM : (rowGSD W (rowTyG Ch P).inv).Ok) {T : Type} {A : T → Type} [∀ t, AddCommGroup (A t)] [∀ t, Module ℂ (A t)]
    {V : Type} [AddCommGroup V] [Module ℂ V] {b : T} (E : V ≃ₗ[ℂ] A b) (tup : TupF TU → T) (h0 : tup (mu0F TU) = b)
    (inj : Function.Injective tup)
    (j : ∀ t : TupF TU, (Fin (((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R t).S.lvlDim
      ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R t).r P.grp P.chr) → X.K) →ₛₗ[σ] A (tup t))
    (li : ∀ t, LinearIndependent ℂ fun i => j t (Pi.single i 1))
    (sp : ∀ t, Submodule.span ℂ (Set.range fun i => j t (Pi.single i 1)) = ⊤)
    (Zs : DefSub (colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).fam3.amb3) :
    ∃ ι : V ≃ₗ[ℂ] (Fin ((rowGSD W (rowTyG Ch P).inv).hDim hM) → ℂ),
      (∀ (t : TupF TU) (ht : tup t = b) (hQ : QE sel (t.1 : Chr X.F X.E X.K) = ∅) y,
        ∃ (F' : (mtildeKGSD W Ch sel t.1).EqFun) (hm : F'.1 ∈ (mtildeGSD W Ch sel t.1 P).EqFun),
          HEq ((mtildeKGSD W Ch sel t.1).res (mtildeKOk W Ch sel t.1 hX) F')
            (((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R t).S.basis.equivFun.symm
              ((((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R t).S.cutE ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R t).r
                (lvlIdem P.grp P.chr)).mulVec y)) ∧
          ι (E.symm (ht ▸ j t y)) = zOfRow W Ch sel t.1 hQ P σ hM ⟨F'.1, hm⟩) ∧
      ∀ (t : TupF TU) (ht : tup t = b) (hQ : QE sel (t.1 : Chr X.F X.E X.K) = ∅)
        (F : Fin (((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).side3 P.grp P.chr Zs).nV t) → X.K),
        ∃ hm : (evC W Ch sel hX v0 TU Xg S0 xiVal trIv P Zs t F).1.1 ∈ (mtildeGSD W Ch sel t.1 P).EqFun,
          ι (E.symm (ht ▸ j t ((((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R t).S.lvlPr
              ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R t).r P.grp P.chr *
            ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R t).vE
              ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.lvl P.grp P.chr)).mulVec F))) =
            zOfRow W Ch sel t.1 hQ P σ hM ⟨_, hm⟩ := by
  have hQ0 := Formalism.L2.DIV.twistPrimes_trivialTuple_empty (X := X) (S := S) sel
  obtain ⟨j', hj, li', sp'⟩ := exists_moved (A := A) h0 E (j (mu0F TU)) (li _) (sp _)
  obtain ⟨ι, hι⟩ := exists_read W Ch sel (mu0F TU).1 hX P hQ0 σ hM j' li' sp'
  refine ⟨ι, fun t e hQ y => ?_, fun t e hQ F => ?_⟩
  · obtain rfl : t = mu0F TU := inj (e.trans h0.symm)
    obtain ⟨F', hm, e1, e2⟩ := hι y
    exact ⟨F', hm, heq_of_eq e1, (congrArg ι (hj y)).symm.trans e2⟩
  · obtain rfl : t = mu0F TU := inj (e.trans h0.symm)
    obtain ⟨F', hm, e1, e2⟩ := hι ((((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R (mu0F TU)).S.lvlPr
              ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R (mu0F TU)).r P.grp P.chr *
            ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R (mu0F TU)).vE
              ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.lvl P.grp P.chr)).mulVec F)
    have e3 : F' = (evC W Ch sel hX v0 TU Xg S0 xiVal trIv P Zs (mu0F TU) F).1 :=
      ((mtildeKGSD W Ch sel (mu0F TU).1).res (mtildeKOk W Ch sel (mu0F TU).1 hX)).injective
        (e1.trans (evC_res_lvl W Ch sel hX v0 TU Xg S0 xiVal trIv P hOk Zs (mu0F TU) F).symm)
    subst e3
    exact ⟨hm, (congrArg ι (hj _)).symm.trans e2⟩

end Gen

section Main

variable {B : Base} {X : PreX B.toPre} {I : TC B X}

theorem tup_heq (ht : I.IsTw) (U : Set I.ι) (X' : Fields) (hx : X' = B.fields) (Pr : Primes X')
    (sel : HeightOneSpectrum (𝓞 X'.F) → HeightOneSpectrum (𝓞 X'.E)) (S : Set ℕ) (tup : I.ι → Tup X'.F X'.E X'.K S)
    (cst : ∀ a, LocCst X' (rowSG Pr sel (tup a))) (idx : ∀ a, ChIdx X' Pr B.R (QE sel (tup a : Chr X'.F X'.E X'.K)))
    (h1 : HEq Pr (B.primes X)) (h2 : HEq sel I.sel) (h3 : S = I.S) (h4 : HEq tup I.tup) (h5 : HEq cst I.cst) (h6 : HEq idx I.idx) :
    HEq (fun t : TupU I U => t.1) (fun t => tup (ixOf I U t)) ∧ HEq (fun t : TupU I U => cstT I t.1) (fun t => cst (ixOf I U t)) ∧
      HEq (fun t : TupU I U => idxT I t.1) (fun t => idx (ixOf I U t)) := by
  subst hx h3
  cases h1
  cases h2
  cases h4
  cases h5
  cases h6
  refine ⟨heq_of_eq (funext fun t => (tup_ixOf I t).symm), Function.hfunext rfl fun t t' e => ?_, Function.hfunext rfl fun t t' e => ?_⟩
  · cases e
    rw [← cstT_tup ht, tup_ixOf]
  · cases e
    rw [← idxT_tup ht, tup_ixOf]

variable (h : I.Ok) (hp : TC.Pins B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (ht : I.IsTw) (hJ : ColIn.JetsIn I)
  (hX : B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc B X → B.LL)) (tr : TrI B X)
  {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : G.Inst (I.rec7 l Z) L} {Gl : G.LatInst (I.rec7 l Z)}
  {Kc : G.Consts} {Y : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Y cX}

theorem iT_heq {t : KerEntTied ex} (hS : I.StdKer l Z t) (τ : (I.rec7 l Z).what₂.Tau) : HEq (t.seam.iT.symm τ) τ := by
  have key : ∀ (X' : Fields) (_ : X' = B.fields) (s : Seam (I.rec7 l Z) X'),
      HEq s (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) → HEq (s.iT.symm τ) τ := by
    intro X' hx s hs
    subst hx
    cases hs
    rfl
  exact key _ hS.X_eq _ hS.seam

abbrev colRecK (t : KerEntTied ex) : ColRec3 B.fields (famC I hX U Xg tr) (lev1 I) (chr1 I) :=
  colRecC h hp l Z ht hJ t.χ (ker_chi_eq I l Z t) hX U Xg tr

section Pins

variable {h hp l Z ht hJ hX U Xg tr} {hOk : (famC I hX U Xg tr).fam3.Ok3 1} {T : Formalism.L2.TiedDataSK ex} {hS : I.StdKer l Z T.ker}
  {Sp : ∀ Zs, SPer ((colRecK h hp l Z ht hJ hX U Xg tr T.ker).face Zs)}
  {R : Member.ExtendedDataRemainder ex (famC I hX U Xg tr) (lev0 I) (chr0 I) (lev1 I) (chr1 I) (colRecK h hp l Z ht hJ hX U Xg tr T.ker).face Sp}
  {htup : R.I.tup = ixOf I U} {hw : ∀ u, R.I.wU u = u}

end Pins

end Main


end GlobalTheory.Mem.R3.SelC

end

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.SelC

theorem pack_heq {D : D7} (p q : Σ' (G : Type) (_ : Group G) (_ : Fintype G) (Pl0 I0 T0 : Type)
      (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m) (C : Formalism.L2.Pj.CoreJ D) (_ : Algebra C.Q.c.F D.what₂.LL)
      (R : RealDat3 D A3 C.Q.c.F) (_ : Face3 D A3), G0 R.Pg D.R.r ≃* G0g D.nd) (e : p = q) :
    letI := p.2.1; letI := p.2.2.1; letI := p.2.2.2.2.2.2.2.2.1; letI := q.2.1; letI := q.2.2.1; letI := q.2.2.2.2.2.2.2.2.1
    (p.1 = q.1 ∧ HEq p.2.1 q.2.1 ∧ p.2.2.2.1 = q.2.2.2.1 ∧ p.2.2.2.2.1 = q.2.2.2.2.1 ∧ p.2.2.2.2.2.1 = q.2.2.2.2.2.1 ∧
      HEq p.2.2.2.2.2.2.1 q.2.2.2.2.2.2.1) ∧
    (HEq p.2.2.2.2.2.2.2.2.2.2.1.P0 q.2.2.2.2.2.2.2.2.2.2.1.P0 ∧ HEq p.2.2.2.2.2.2.2.2.2.2.1.ψ0 q.2.2.2.2.2.2.2.2.2.2.1.ψ0 ∧
      HEq p.2.2.2.2.2.2.2.2.2.2.1.P1 q.2.2.2.2.2.2.2.2.2.2.1.P1 ∧ HEq p.2.2.2.2.2.2.2.2.2.2.1.ψ1 q.2.2.2.2.2.2.2.2.2.2.1.ψ1 ∧
      HEq p.2.2.2.2.2.2.2.2.2.2.1.Dc q.2.2.2.2.2.2.2.2.2.2.1.Dc ∧ HEq p.2.2.2.2.2.2.2.2.2.2.1.Sp q.2.2.2.2.2.2.2.2.2.2.1.Sp) ∧
    HEq (zsOf p.2.2.2.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.2.2.2.1) (zsOf q.2.2.2.2.2.2.2.2.2.1 q.2.2.2.2.2.2.2.2.2.2.1) ∧
    HEq (p.2.2.2.2.2.2.2.2.2.2.1.Dc (zsOf p.2.2.2.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.2.2.2.1))
      (q.2.2.2.2.2.2.2.2.2.2.1.Dc (zsOf q.2.2.2.2.2.2.2.2.2.1 q.2.2.2.2.2.2.2.2.2.2.1)) ∧
    HEq (p.2.2.2.2.2.2.2.2.2.2.1.Sp (zsOf p.2.2.2.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.2.2.2.1))
      (q.2.2.2.2.2.2.2.2.2.2.1.Sp (zsOf q.2.2.2.2.2.2.2.2.2.1 q.2.2.2.2.2.2.2.2.2.2.1)) ∧
    (p.2.2.2.2.2.2.2.2.2.2.1.Dc (zsOf p.2.2.2.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.2.2.2.1)).Mem =
      (q.2.2.2.2.2.2.2.2.2.2.1.Dc (zsOf q.2.2.2.2.2.2.2.2.2.1 q.2.2.2.2.2.2.2.2.2.2.1)).Mem := by
  subst e
  exact ⟨⟨rfl, HEq.rfl, rfl, rfl, rfl, HEq.rfl⟩, ⟨HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩, HEq.rfl, HEq.rfl, HEq.rfl, rfl⟩

theorem heq_app {A M M' : Type} (e : M = M') {f : A → M} {g : A → M'} (h : HEq f g) (u : A) : HEq (f u) (g u) := by
  subst e
  cases h
  rfl

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}


variable {L : SizeData₂ (w.st Z).toD7} {hT : GatTies (w.st Z).toD7} {Gi : Formalism.MainNotions.G.Inst (w.st Z).toD7 L} {Gl : Formalism.MainNotions.G.LatInst (w.st Z).toD7}
  {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (w.st Z).toD7} {cX : ExtraC} {ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX}




attribute [local instance] Formalism.BasicNotions.Host.cmStar


end GlobalTheory.Mem.R3.SelC

end
end
end
