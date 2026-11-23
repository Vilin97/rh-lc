module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelsTwG
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalRingCardinality.DataLevel
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LocIdFr
public import Mathlib.RingTheory.Valuation.Integral
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocLEqIntVOfDvdUnit

section

@[expose] public section

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory

theorem natCast_inv_mem_adicCompletionIntegers {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (T : ℕ) (hT : (T : 𝓞 F) ∉ v.asIdeal) :
    ((T : v.adicCompletion F) ≠ 0) ∧ (T : v.adicCompletion F)⁻¹ ∈ v.adicCompletionIntegers F := by
  have h1 : Valued.v (((T : 𝓞 F) : F) : v.adicCompletion F) = 1 := by
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := F) (v := v)).2 hT
  have h2 : (((T : 𝓞 F) : F) : v.adicCompletion F) = (T : v.adicCompletion F) := by
    have : ((T : 𝓞 F) : F) = (T : F) := by push_cast; rfl
    rw [this]
    exact map_natCast (algebraMap F (v.adicCompletion F)) T
  rw [h2] at h1
  have hne : (T : v.adicCompletion F) ≠ 0 := by
    intro h; rw [h, map_zero] at h1; exact zero_ne_one h1
  refine ⟨hne, ?_⟩
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, h1, inv_one]

theorem locL_eq_intV_of_dvd_unit {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
    [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E)) (P : Fin n → Prop)
    (π c : 𝓞 E) (T : ℕ) (hT : (T : 𝓞 F) ∉ v.asIdeal) (hπc : π * c = (T : 𝓞 E))
    (hΛ : ∀ y, y ∈ Λ ↔ ∀ a, ∃ r : 𝓞 E, y a = r ∧ (P a → π ∣ r)) (y : Fin n → E ⊗[F] v.adicCompletion F) :
    (y ∈ Formalism.L2.Herm.locL v Λ ↔ ∀ a, y a ∈ Formalism.BasicNotions.intV E v) := by
  classical
  have hleft : ∀ r : 𝓞 E, ((r : E) ⊗ₜ[F] (1 : v.adicCompletion F)) ∈ Formalism.BasicNotions.intV E v := fun r =>
    Subring.subset_closure (Or.inl ⟨⟨(r : E), ⟨r, rfl⟩⟩, rfl⟩)
  have hright : ∀ t ∈ v.adicCompletionIntegers F, ((1 : E) ⊗ₜ[F] t) ∈ Formalism.BasicNotions.intV E v := fun t ht =>
    Subring.subset_closure (Or.inr ⟨⟨t, ht⟩, rfl⟩)
  constructor
  · intro hy
    let M : Submodule (Formalism.BasicNotions.intV E v) (Fin n → E ⊗[F] v.adicCompletion F) :=
      { carrier := {y | ∀ a, y a ∈ Formalism.BasicNotions.intV E v}
        add_mem' := fun ha hb a => (Formalism.BasicNotions.intV E v).add_mem (ha a) (hb a)
        zero_mem' := fun _ => (Formalism.BasicNotions.intV E v).zero_mem
        smul_mem' := fun s _ hy a => (Formalism.BasicNotions.intV E v).mul_mem s.2 (hy a) }
    have hle : Formalism.L2.Herm.locL v Λ ≤ M := by
      unfold Formalism.L2.Herm.locL Formalism.UG.latS
      rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩ a
      obtain ⟨r, hr, -⟩ := (hΛ x).1 hx a
      show Formalism.UG.inclE _ (x a) ∈ Formalism.BasicNotions.intV E v
      rw [hr]; exact hleft r
    exact hle hy
  · intro hy
    obtain ⟨_, hinv⟩ := natCast_inv_mem_adicCompletionIntegers v T hT
    have he : ∀ a, (Pi.single a (1 : E ⊗[F] v.adicCompletion F)) ∈ Formalism.L2.Herm.locL v Λ := by
      intro a
      have hx : (Pi.single a ((π : 𝓞 E) : E) : Fin n → E) ∈ Λ := by
        rw [hΛ]
        intro b
        refine ⟨(Pi.single a π : Fin n → 𝓞 E) b, ?_, fun _ => ?_⟩
        · by_cases h : b = a
          · subst h; simp
          · simp [h]
        · by_cases h : b = a
          · subst h; simp
          · simp [h]
      have hg : (Pi.single a (((π : E)) ⊗ₜ[F] (1 : v.adicCompletion F)) : Fin n → _) ∈
          Formalism.L2.Herm.locL v Λ := by
        unfold Formalism.L2.Herm.locL Formalism.UG.latS
        apply Submodule.subset_span
        refine ⟨_, hx, ?_⟩
        funext b
        by_cases h : b = a
        · subst h; simp [Formalism.UG.inclE]
        · simp [h, Formalism.UG.inclE]
      let s : Formalism.BasicNotions.intV E v :=
        ⟨((c : E) ⊗ₜ[F] (1 : v.adicCompletion F)) * ((1 : E) ⊗ₜ[F] (T : v.adicCompletion F)⁻¹),
          (Formalism.BasicNotions.intV E v).mul_mem (hleft c) (hright _ hinv)⟩
      have hs : (s : E ⊗[F] v.adicCompletion F) * ((π : E) ⊗ₜ[F] (1 : v.adicCompletion F)) = 1 := by
        obtain ⟨hne, -⟩ := natCast_inv_mem_adicCompletionIntegers v T hT
        show ((c : E) ⊗ₜ[F] (1 : v.adicCompletion F)) * ((1 : E) ⊗ₜ[F] (T : v.adicCompletion F)⁻¹) *
          ((π : E) ⊗ₜ[F] (1 : v.adicCompletion F)) = 1
        simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
        have hcπ : (c : E) * (π : E) = (T : E) := by
          rw [mul_comm]; exact_mod_cast congrArg (fun z : 𝓞 E => (z : E)) hπc
        rw [hcπ]
        have hT1 : (T : E) ⊗ₜ[F] (1 : v.adicCompletion F) = (1 : E) ⊗ₜ[F] (T : v.adicCompletion F) := by
          have e1 := map_natCast (Algebra.TensorProduct.includeLeftRingHom (R := F) (A := E)
            (B := v.adicCompletion F)) T
          have e2 := map_natCast (Algebra.TensorProduct.includeRight (R := F) (A := E)
            (B := v.adicCompletion F)) T
          rw [Algebra.TensorProduct.includeLeftRingHom_apply] at e1
          rw [Algebra.TensorProduct.includeRight_apply] at e2
          rw [e1, e2]
        calc (T : E) ⊗ₜ[F] (T : v.adicCompletion F)⁻¹
            = ((T : E) ⊗ₜ[F] (1 : v.adicCompletion F)) * ((1 : E) ⊗ₜ[F] (T : v.adicCompletion F)⁻¹) := by
              simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
          _ = 1 := by
              rw [hT1, Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_inv_cancel₀ hne]
              rfl
      have := (Formalism.L2.Herm.locL v Λ).smul_mem s hg
      convert this using 1
      funext b
      by_cases h : b = a
      · subst h
        rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul, Pi.single_eq_same, Pi.single_eq_same, hs]
      · rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul, Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, mul_zero]
    have hsum : y = ∑ a, (⟨y a, hy a⟩ : Formalism.BasicNotions.intV E v) • Pi.single a (1 : E ⊗[F] v.adicCompletion F) := by
      funext b
      rw [Finset.sum_apply, Finset.sum_eq_single b]
      · rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul, Pi.single_eq_same, mul_one]
      · intro a _ hab
        rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul, Pi.single_eq_of_ne (Ne.symm hab), mul_zero]
      · intro h; exact absurd (Finset.mem_univ b) h
    rw [hsum]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (he a)

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocLEqIntVOfDvdUnitStatement

section

@[expose] public section

open NumberField IsDedekindDomain
open scoped TensorProduct

theorem _root_.GlobalTheory.T.mem_locL_iff_forall_mem_intV_of_not_mem : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E)) (P : Fin n → Prop) (π c : 𝓞 E) (T : ℕ),
    (T : 𝓞 F) ∉ v.asIdeal → π * c = (T : 𝓞 E) →
    (∀ y, y ∈ Λ ↔ ∀ a, ∃ r : 𝓞 E, y a = r ∧ (P a → π ∣ r)) → ∀ (y : Fin n → E ⊗[F] v.adicCompletion F),
    (y ∈ Formalism.L2.Herm.locL v Λ ↔ ∀ a, y a ∈ Formalism.BasicNotions.intV E v) := by
  first | exact @GlobalTheory.locL_eq_intV_of_dvd_unit | exact GlobalTheory.locL_eq_intV_of_dvd_unit | (intros; apply GlobalTheory.locL_eq_intV_of_dvd_unit <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplittingFstMemIntegers

section

@[expose] public section

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory

theorem adicCompletion_mem_integers_of_isIntegral_int {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) {y : v.adicCompletion F} (hy : IsIntegral ℤ y) :
    y ∈ v.adicCompletionIntegers F := by
  let O := v.adicCompletionIntegers F
  have hint : (Valued.v : Valuation (v.adicCompletion F) _).Integers O :=
    Valuation.integer.integers _
  have hy' : IsIntegral O y := hy.tower_top
  exact hint.mem_of_integral hy'

theorem splitting_fst_mem_integers : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (spl : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F),
    (∀ a : v.adicCompletion F, spl ((1 : E) ⊗ₜ[F] a) = (a, a)) →
    ∀ z ∈ Formalism.BasicNotions.intV E v, (spl z).1 ∈ v.adicCompletionIntegers F := by
  apply Formalism.MainNotions.Gaps.Loc.fst_int <;> assumption

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplittingFstMemIntegersStatement

section

@[expose] public section

open NumberField IsDedekindDomain
open scoped TensorProduct

theorem _root_.GlobalTheory.T.splitting_fst_mem_integers' : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (spl : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F),
    (∀ a : v.adicCompletion F, spl ((1 : E) ⊗ₜ[F] a) = (a, a)) →
    ∀ z ∈ Formalism.BasicNotions.intV E v, (spl z).1 ∈ v.adicCompletionIntegers F := by
  first | exact @GlobalTheory.splitting_fst_mem_integers | exact GlobalTheory.splitting_fst_mem_integers | (intros; apply GlobalTheory.splitting_fst_mem_integers <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOrthonormalStepBasisBaseLatticeCharts

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.G Formalism.L2.G Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.UG
open scoped TensorProduct

namespace GlobalTheory.Mem.Top.KerTwLv




theorem stepBasis_std : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (n : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ (Fl : ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
        G.Fills ((w.D Z).gat u v hg)),
      ∀ (hfl : ∀ u v hg, (Fl u v hg).t = (w.D Z).R.t ∧ (Fl u v hg).mm = (w.D Z).R.m),
      (∀ u v hg (x : Fin ((w.D Z).gat u v hg).P.nV) (s : Fin (((w.D Z).gat u v hg).P.n' x)), ∀ j ∈ SizeData₂.lifts (w.D Z),
        ((Fl u v hg).w x j s : ℝ) = wj (w.D Z) j (t.Gt.gat_pos u v hg ⟨x, s⟩) - G.kaJ (w.D Z) j) →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      ∀ (hμ : (w.D Z).what₂.muAt v ≠ (w.D Z).what₂.mu0),
      ∀ (tt : Formalism.L2.Forms.SymmetricTwistedColumnsAtPrimes n.tp t.C (w.tw Z)), TC.StdTw w.I w.l Z w.l0 tt →
      ∀ j (hj : j + 1 ≤ (w.D Z).R.m), ∃ B : GL (Fin ((w.D Z).sp.X (j + 1)).rank) (w.D Z).host.E,
        cT (sigD (w.D Z) : (w.D Z).host.E →+* (w.D Z).host.E)
          (reGL (rankN (w.D Z) (j + 1) hj) (w.D Z).host.E B).1 * gramN (w.D Z) (j + 1) hj *
          (reGL (rankN (w.D Z) (j + 1) hj) (w.D Z).host.E B).1 = 1 ∧
        ∀ (β : tt.ch.Ch u ((w.D Z).what₂.muAt v) (j + 1)) w' h (x : Fin ((w.D Z).sp.X (j + 1)).rank → w'.adicCompletion (w.D Z).host.F),
          (∃ y ∈ Formalism.L2.Herm.locL w' (tt.ch.lev u ((w.D Z).what₂.muAt v) (j + 1) (Formalism.MainNotions.G.CmpJ.AgreeLv.one_le j) hj β).Lb,
            ∀ a, ((t.g.herm.g u v hg).spl w' h (y a)).1 = x a) ↔
          ∀ a, (((GlobalTheory.Mem.Top.KerTwLv.frOf t.g.herm u v hg B w' h)⁻¹ :
            GL (Fin ((w.D Z).sp.X (j + 1)).rank) (w'.adicCompletion (w.D Z).host.F)) :
              Matrix (Fin ((w.D Z).sp.X (j + 1)).rank) (Fin ((w.D Z).sp.X (j + 1)).rank) (w'.adicCompletion (w.D Z).host.F)).mulVec x a ∈
            w'.adicCompletionIntegers (w.D Z).host.F := by
  intro K B f T w hK hF hP Z t Wt nch n Y hmu hQp O hstdO hunf E hent Fl hfl hwt u v hg hμ tt hstd j hj
  have hsc := (GlobalTheory.Mem.Col2.TC.spaces_in_coordinates w.I w.ok w.pins w.l Z).2.2.2 (j+1) hj
  obtain ⟨k, hk⟩ := hstd.1.reads u ((w.D Z).what₂.muAt v) hμ (j+1) (Formalism.MainNotions.G.CmpJ.AgreeLv.one_le j) hj
  have hcar := tt.forms.car u ((w.D Z).what₂.muAt v) hμ (j+1) (Formalism.MainNotions.G.CmpJ.AgreeLv.one_le j) hj
  refine ⟨1, ?_, ?_⟩
  · rw [hsc.1]
    simp [cT, Matrix.map_one]
  · intro β w' h x
    have hfr : GlobalTheory.Mem.Top.KerTwLv.frOf t.g.herm u v hg (1 : GL (Fin ((w.D Z).sp.X (j + 1)).rank) (w.D Z).host.E) w' h = 1 :=
      map_one _
    rw [hfr, inv_one]
    simp only [Units.val_one, Matrix.one_mulVec]
    have hT : ((((w.D Z).mem u).A.T : ℕ) : 𝓞 (w.D Z).host.F) ∉ w'.asIdeal := by
      intro hT
      have hcop : Nat.Coprime ((w.D Z).what₂.places.resChar v) ((w.D Z).mem u).A.T :=
        (Nat.Prime.coprime_iff_not_dvd hg.1).2 hg.2.2.2.2.2
      obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hcop
      apply w'.isPrime.ne_top
      rw [Ideal.eq_top_iff_one]
      have e : ((1 : ℤ) : 𝓞 (w.D Z).host.F) = (a : 𝓞 (w.D Z).host.F) * (((w.D Z).what₂.places.resChar v : ℕ) : 𝓞 (w.D Z).host.F)
          + (b : 𝓞 (w.D Z).host.F) * ((((w.D Z).mem u).A.T : ℕ) : 𝓞 (w.D Z).host.F) := by
        rw [← hab]; push_cast; ring
      rw [Int.cast_one] at e
      rw [e]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h) (Ideal.mul_mem_left _ _ hT)
    have hLb : ∀ y, y ∈ (tt.ch.lev u ((w.D Z).what₂.muAt v) (j + 1) (Formalism.MainNotions.G.CmpJ.AgreeLv.one_le j) hj β).Lb ↔
        ∀ a, ∃ r : 𝓞 (w.D Z).host.E, y a = r ∧ (a.1 + 1 = ((w.D Z).sp.X (j + 1)).rank → (w.px.piT u : 𝓞 (w.D Z).host.E) ∣ r) := by
      intro y
      have e1 := (hcar β).Lb_eq
      have e2 := hk.lb β
      have hr := rankN (w.D Z) (j + 1) hj
      have hmap : y ∈ (tt.ch.lev u ((w.D Z).what₂.muAt v) (j + 1) (Formalism.MainNotions.G.CmpJ.AgreeLv.one_le j) hj β).Lb ↔
          reV (rankN (w.D Z) (j + 1) hj) (w.D Z).host.E y ∈
            reL (rankN (w.D Z) (j + 1) hj) (tt.ch.lev u ((w.D Z).what₂.muAt v) (j + 1) (Formalism.MainNotions.G.CmpJ.AgreeLv.one_le j) hj β).Lb := by
        constructor
        · intro hy
          exact ⟨y, hy, rfl⟩
        · rintro ⟨z, hz, hzy⟩
          have : z = y := (reV (rankN (w.D Z) (j + 1) hj) (w.D Z).host.E).injective hzy
          exact this ▸ hz
      rw [hmap, ← e1]
      refine (e2 _).trans ?_
      simp only [TC.baseL, Set.mem_setOf_eq, reV, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply]
      constructor
      · intro H a
        obtain ⟨r, hr1, hr2⟩ := H (finCongr hr a)
        refine ⟨r, ?_, fun ha => hr2 ?_⟩
        · rw [LinearMap.funLeft_apply, Equiv.symm_apply_apply] at hr1
          exact hr1
        · have e : ((finCongr hr a : Fin _) : ℕ) = a := rfl
          rw [e]
          exact ha.trans hr
      · intro H b
        obtain ⟨r, hr1, hr2⟩ := H ((finCongr hr).symm b)
        refine ⟨r, hr1, fun hb => hr2 ?_⟩
        have e : (((finCongr hr).symm b : Fin _) : ℕ) = b := rfl
        rw [e]
        exact hb.trans hr.symm
    have hπ : (w.px.piT u : 𝓞 (w.D Z).host.E) * (B.fields.conjO (w.px.piT u) : 𝓞 (w.D Z).host.E) =
        ((((w.D Z).mem u).A.T : ℕ) : 𝓞 (w.D Z).host.E) :=
      B.primes_piT_norm w.px u
    have L := @GlobalTheory.T.mem_locL_iff_forall_mem_intV_of_not_mem (w.D Z).host.F (w.D Z).host.E _ _ _ _ _ _ w' _ _ _ _ _ _ hT hπ hLb
    have PI := @GlobalTheory.T.splitting_fst_mem_integers' (w.D Z).host.F (w.D Z).host.E _ _ _ _ _ w' _ ((t.g.herm.g u v hg).spl_alg w' h)
    constructor
    · rintro ⟨y, hy, hyx⟩ a
      rw [← hyx a]
      exact PI _ ((L y).1 hy a)
    · intro hx
      refine ⟨fun a => (1 : (w.D Z).host.E) ⊗ₜ[(w.D Z).host.F] x a, (L _).2
        (fun a => Subring.subset_closure (Or.inr ⟨⟨x a, hx a⟩, rfl⟩)), fun a => ?_⟩
      rw [(t.g.herm.g u v hg).spl_alg]

end GlobalTheory.Mem.Top.KerTwLv
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOrthonormalStepBasisBaseLatticeChartsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.G Formalism.L2.G Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.UG

theorem _root_.GlobalTheory.T.exists_orthonormal_step_basis_base_lattice_charts : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (n : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ (Fl : ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
        G.Fills ((w.D Z).gat u v hg)),
      ∀ (hfl : ∀ u v hg, (Fl u v hg).t = (w.D Z).R.t ∧ (Fl u v hg).mm = (w.D Z).R.m),
      (∀ u v hg (x : Fin ((w.D Z).gat u v hg).P.nV) (s : Fin (((w.D Z).gat u v hg).P.n' x)), ∀ j ∈ SizeData₂.lifts (w.D Z),
        ((Fl u v hg).w x j s : ℝ) = wj (w.D Z) j (t.Gt.gat_pos u v hg ⟨x, s⟩) - G.kaJ (w.D Z) j) →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      ∀ (hμ : (w.D Z).what₂.muAt v ≠ (w.D Z).what₂.mu0),
      ∀ (tt : Formalism.L2.Forms.SymmetricTwistedColumnsAtPrimes n.tp t.C (w.tw Z)), TC.StdTw w.I w.l Z w.l0 tt →
      ∀ j (hj : j + 1 ≤ (w.D Z).R.m), ∃ B : GL (Fin ((w.D Z).sp.X (j + 1)).rank) (w.D Z).host.E,
        cT (sigD (w.D Z) : (w.D Z).host.E →+* (w.D Z).host.E)
          (reGL (rankN (w.D Z) (j + 1) hj) (w.D Z).host.E B).1 * gramN (w.D Z) (j + 1) hj *
          (reGL (rankN (w.D Z) (j + 1) hj) (w.D Z).host.E B).1 = 1 ∧
        ∀ (β : tt.ch.Ch u ((w.D Z).what₂.muAt v) (j + 1)) w' h (x : Fin ((w.D Z).sp.X (j + 1)).rank → w'.adicCompletion (w.D Z).host.F),
          (∃ y ∈ Formalism.L2.Herm.locL w' (tt.ch.lev u ((w.D Z).what₂.muAt v) (j + 1) (Formalism.MainNotions.G.CmpJ.AgreeLv.one_le j) hj β).Lb,
            ∀ a, ((t.g.herm.g u v hg).spl w' h (y a)).1 = x a) ↔
          ∀ a, (((GlobalTheory.Mem.Top.KerTwLv.frOf t.g.herm u v hg B w' h)⁻¹ :
            GL (Fin ((w.D Z).sp.X (j + 1)).rank) (w'.adicCompletion (w.D Z).host.F)) :
              Matrix (Fin ((w.D Z).sp.X (j + 1)).rank) (Fin ((w.D Z).sp.X (j + 1)).rank) (w'.adicCompletion (w.D Z).host.F)).mulVec x a ∈
            w'.adicCompletionIntegers (w.D Z).host.F := by
  first | exact @GlobalTheory.Mem.Top.KerTwLv.stepBasis_std | exact GlobalTheory.Mem.Top.KerTwLv.stepBasis_std | (intros; apply GlobalTheory.Mem.Top.KerTwLv.stepBasis_std <;> assumption)
end
end
