module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.EmbAlg
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.GlobNegOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.FinMulSupp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.MemCenterSupExistsScalarMul
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.JstdTrace
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.FinD
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.OneD
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.IotaEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.NormalOfCenter
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.GqS

section

@[expose] public section

open NumberField UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

theorem UpperTheory.V.Z.Sym.Glob.gqS :
    UpperTheory.V.Z.Sym.Glob.GqS := by
  intro F _ _ Δ D hD ι hι t ht τ hτ γ j hγ hj
  haveI := hD.real
  have hreg : τ ^ 2 - 4 ≠ 0 := cm_ne hτ
  have htr : ∀ (g : DX Δ) (v : Pl F), HasTr g τ → HasTr ((ι g).1 v) (cv v τ) :=
    fun g v hg => hasTr_map (cv v) (hι g v) hg
  by_cases hA : D.admitted t τ
  · rw [show one (D.admitted t τ) = 1 from if_pos hA, one_mul]
    refine gqD D hD ι hι t ht τ hτ hA γ j hγ hj γ (D.fSv t) ?_ (fun v => ((D.S v).cS : ℂ))
      (fun v => gOrb (Ov v) (jstd ((cv v) τ)) 1 (toUnit QuadraticAlgebra.omega)) ?_
    · intro v u hu x
      by_cases hv : v ∈ D.Sg
      · have hS := hD.sig v hv
        have hu' : u ∈ (D.S v).J2 := by simpa [Dat.J2v, hv] using hu
        simp only [Dat.fSv, if_pos hv]
        rw [(hS.S_inv (t v) (ht v hv) u hu' _).2, (hS.S_inv (t v) (ht v hv) u⁻¹ (inv_mem hu') _).1]
      · have hu' : u ∈ KD ((cv v) Δ) (Ov v) := by simpa [Dat.J2v, hv] using hu
        have hiff : u⁻¹ * x * u ∈ KD ((cv v) Δ) (Ov v) ↔ x ∈ KD ((cv v) Δ) (Ov v) := by
          rw [(KD ((cv v) Δ) (Ov v)).mul_mem_cancel_right hu',
            (KD ((cv v) Δ) (Ov v)).mul_mem_cancel_left (inv_mem hu')]
        simp only [Dat.fSv, if_neg hv, one]
        by_cases hx : x ∈ KD ((cv v) Δ) (Ov v)
        · rw [if_pos hx, if_pos (hiff.2 hx)]
        · rw [if_neg hx, if_neg (fun h => hx (hiff.1 h))]
    · intro v jv hjv
      have hgv : HasTr ((ι γ).1 v) (cv v τ) := htr γ v hγ
      have hrv := cv_reg hreg v
      obtain ⟨z, hz⟩ := zEx hrv
      refine ⟨emb_comm hjv, ?_⟩
      by_cases hv : v ∈ D.Sg
      · have hS := hD.sig v hv
        obtain ⟨hF, -, hO, -, -⟩ := hS.D_orb (t v) (ht v hv) _ _ jv hrv hgv hjv z hz
        have e1 : D.fSv t v = (D.S v).fS (t v) := by
          funext g
          simp [Dat.fSv, hv]
        have e2 : D.J2v v = (D.S v).J2 := by simp [Dat.J2v, hv]
        rw [e1, e2]
        refine ⟨hF, fun _ => ?_, fun h => absurd hv h⟩
        rw [hO, show one (Ind _ _ _) = 1 from if_pos (hA v hv), mul_one]
      · have hL := hD.off v hv
        have e1 : D.fSv t v = fun g => one (g ∈ KD ((cv v) Δ) (Ov v)) := by
          funext g
          simp [Dat.fSv, hv]
        have e2 : D.J2v v = KD ((cv v) Δ) (Ov v) := by simp [Dat.J2v, hv]
        rw [e1, e2]
        refine ⟨(finD _ _ _ _ hL hrv _ jv hgv hjv).1, fun h => absurd h hv, fun _ =>
          ⟨(locD _ _ _ _ hL hrv _ jv hgv hjv (D.χ v) (hD.chi v).1 z hz).1, fun hK hu =>
            ⟨if_pos hK, fun y hy => ?_⟩⟩⟩
        have hy' : y⁻¹ * (ι γ).1 v * y ∈ ZD ((cv v) Δ) ⊔ KD ((cv v) Δ) (Ov v) := by
          by_contra hn
          exact hy (if_neg (fun h => hn (le_sup_right (a := ZD ((cv v) Δ)) h)))
        exact (oneD _ _ _ _ hL hrv _ jv hgv hjv hK hu).2.1 y hy'
  · rw [show one (D.admitted t τ) = 0 from if_neg hA, zero_mul, mul_zero]
    apply gqOn_zero
    intro y
    obtain ⟨v, hv, hI⟩ : ∃ v ∈ D.Sg, ¬ Ind (D.S v).H ((cv v) τ) (t v) := by
      simpa [Dat.admitted] using hA
    have heq : ((Quotient.out y)⁻¹ * ι γ * Quotient.out y).1 v =
        ((Quotient.out y).1 v)⁻¹ * (ι γ).1 v * (Quotient.out y).1 v := rfl
    have hgtr : HasTr (((Quotient.out y)⁻¹ * ι γ * Quotient.out y).1 v) (cv v τ) := by
      rw [heq]
      exact hasTr_conj (htr γ v hγ) _
    have hz : D.fSv t v (((Quotient.out y)⁻¹ * ι γ * Quotient.out y).1 v) = 0 := by
      simp only [Dat.fSv, if_pos hv]
      by_contra hne
      exact hI ((hD.sig v hv).S_supp (t v) (ht v hv) _ _ hgtr hne)
    exact fin_mulSupp (D.fSv t) D.Sg (fun w hw k hk => by simp [Dat.fSv, hw, one, hk]) _ hz
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.QuaternionStableSideTraceIdentity

section

@[expose] public section

namespace UpperTheory.V.Z.Sym.Glob

open NumberField Loc

private theorem aux_statement_10 {F : Type} [Field F] [NumberField F] {Δ : F} (D : Dat Δ) (hD : D.Ok) (t : Dat.Par F)
    (ht : D.Cone t) (τ : F) (h : D.admitted t τ) : τ ^ 2 - 4 ≠ 0 := by
  intro h0
  obtain ⟨v, hv⟩ := hD.ne
  refine ((hD.sig v hv).reg (t v) (ht v hv) _ (h v hv)).2 ?_
  have h2 : IsIntegral (Ov v) (2 : Kv v) := by
    have := isIntegral_algebraMap (R := Ov v) (A := Kv v) (x := 2)
    rwa [map_ofNat] at this
  have h1 : (τ - 2) * (τ + 2) = 0 := by rw [← h0]; ring
  rcases mul_eq_zero.mp h1 with h1 | h1
  · rw [sub_eq_zero.mp h1, map_ofNat]; exact h2
  · rw [eq_neg_of_add_eq_zero_left h1, map_neg, map_ofNat]; exact h2.neg

private theorem sum_sub {α : Type} (p : α → Prop) (f : α → ℂ) (c : ℂ) :
    ∑ᶠ i : {a // p a}, c * f i.1 = c * ∑ᶠ a, one (p a) * f a := by
  classical
  have h1 : ∑ᶠ i : {a // p a}, c * f i.1 = ∑ᶠ (a) (_ : p a), c * f a :=
    finsum_subtype_eq_finsum_cond (f := fun a => c * f a) p
  rw [h1]
  have h2 : ∀ a, ∑ᶠ (_ : p a), c * f a = c • (one (p a) * f a) := by
    intro a
    rw [finsum_eq_if, smul_eq_mul]
    unfold one
    split_ifs <;> simp
  simp_rw [h2]
  rw [← smul_finsum, smul_eq_mul]


theorem split_side_identity_unitary : QuaternionStableSideTraceIdentity := by
  intro F _ _ Δ D hD x₀ hx₀
  obtain ⟨-, ⟨ι, hι⟩, -⟩ := iotaEx F Δ
  obtain ⟨n, x, c, hx0, hoff, hc, hsum⟩ := fibre F Δ D hD ι hι x₀ hx₀
  have hΔ : Δ ≠ 0 := by
    obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
    obtain ⟨σ⟩ : Nonempty (F →+* ℝ) := ⟨InfinitePlace.embedding_of_isReal (hD.real.isReal w)⟩
    have hneg : σ Δ < 0 := hD.neg σ
    intro h0
    rw [h0, map_zero] at hneg
    exact lt_irrefl _ hneg
  refine ⟨n, x, c * ∏ v ∈ D.Sg, (D.S v).cS, hx0, hoff, ?_, ?_⟩
  · exact mul_pos hc (Finset.prod_pos fun v hv => (hD.sig v hv).cS)
  · intro V _ _ _ ch B hB t ht
    classical
    have hG : ∀ a, D.Good t a ↔ IsCM a ∧ D.admitted t a := fun a => Iff.rfl
    have hex : ∀ s : {a // D.Good t a}, ∃ g : DX Δ, HasTr g s.1 :=
      fun s => (embEx F Δ D hD s.1).1 ((hG _).1 s.2).1
    choose γ hγ using hex
    have hreg : ∀ s : {a // D.Good t a}, s.1 ^ 2 - 4 ≠ 0 :=
      fun s => aux_statement_10 D hD t ht s.1 ((hG _).1 s.2).2
    have hj : ∀ s : {a // D.Good t a}, ∃ j : (Etau F s.1)ˣ →* DX Δ, IsEmb s.1 (γ s) j :=
      fun s => (embAlg F Δ s.1 hΔ (hreg s) (γ s) (hγ s)).1
    choose j hjj using hj
    rw [hsum V ch B hB t ht {a // D.Good t a} (fun s => s.1) γ j Subtype.val_injective
      (fun s => ⟨hreg s, hγ s, hjj s⟩) ?_]
    · have hterm : ∀ s : {a // D.Good t a},
          ch s.1 * gqOn (ι.comp (j s)) (scalE s.1) D.UZ
            (fun y => D.FS t ((Quotient.out y)⁻¹ * ι (γ s) * Quotient.out y)) =
            (∏ v ∈ D.Sg, ((D.S v).cS : ℂ)) * (ch s.1 * ms s.1 * D.nS s.1) := by
        intro s
        rw [gqS F Δ D hD ι hι t ht s.1 ((hG _).1 s.2).1 (γ s) (j s) (hγ s) (hjj s)]
        have h1 : one (D.admitted t s.1) = 1 := if_pos ((hG _).1 s.2).2
        rw [h1]
        ring
      rw [finsum_congr hterm, sum_sub (fun a => D.Good t a) (fun a => ch a * ms a * D.nS a)]
      unfold Dat.sumS
      push_cast
      ring
    · intro g s hg hs
      exact ⟨⟨s, (hG s).2 ⟨(embEx F Δ D hD s).2 g hg (aux_statement_10 D hD t ht s hs), hs⟩⟩, rfl⟩

end UpperTheory.V.Z.Sym.Glob
end
end
