module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConcrete
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TieTrF
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsEmbeddingOfRingTie
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsTiedOfIsRecG
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.FullTiedCBase
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TieIwLevTieOf
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Presheaf
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.SelfDualAtColLevel

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalIdentificationPlaceEqInducedRealPlace

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G NumberField IsDedekindDomain Formalism.UG Formalism.L2.Forms
attribute [local instance] Formalism.BasicNotions.factResChar Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TiePlace

theorem iota_sigma_mem_range {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [Field Qq] [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O} (S : HidaSetting p n' W Qq O Kf ι σ j w) (s : ℕ) (y : Qq) :
    ι ((σ ^ s) y) ∈ Set.range (algebraMap O Kf) ↔ y ∈ Set.range (algebraMap W Qq) := by
  haveI := S.frac_alt
  haveI := S.frac_O

  have h1 : ∀ z : Qq, z ∈ Set.range (algebraMap W Qq) → σ z ∈ Set.range (algebraMap W Qq) := by
    rintro _ ⟨t, rfl⟩
    obtain ⟨t', ht'⟩ := S.frob t
    exact ⟨_, ht'.symm⟩
  have hk : ∀ (k : ℕ) (z : Qq), z ∈ Set.range (algebraMap W Qq) → (σ ^ k) z ∈ Set.range (algebraMap W Qq) := by
    intro k
    induction k with
    | zero => intro z hz; simpa using hz
    | succ k ih =>
      intro z hz
      rw [pow_succ]
      exact ih _ (h1 z hz)
  have hs : ∀ z : Qq, (σ ^ s) z ∈ Set.range (algebraMap W Qq) ↔ z ∈ Set.range (algebraMap W Qq) := by
    intro z
    refine ⟨fun h => ?_, hk s z⟩
    have hn : 1 ≤ n' := le_trans (by norm_num) S.two_le
    have e : (σ ^ (s * (n' - 1))) ((σ ^ s) z) = z := by
      have em : (σ ^ (s * (n' - 1))) ((σ ^ s) z) = (σ ^ (s * (n' - 1)) * σ ^ s) z := rfl
      rw [em, ← pow_add]
      have : s * (n' - 1) + s = n' * s := by
        obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
        simp only [Nat.add_sub_cancel_left]
        ring
      rw [this, pow_mul, S.period, one_pow]
      rfl
    rw [← e]
    exact hk _ _ h

  have hj : Function.Injective j := by
    intro a b h
    apply IsFractionRing.injective W Qq
    apply ι.injective
    rw [S.ι_comp, S.ι_comp, h]
  have hnu : ¬ IsUnit (p : O) := by
    letI := j.toAlgebra
    haveI : Module.Finite W O := S.finite
    haveI : FaithfulSMul W O := (faithfulSMul_iff_algebraMap_injective _ _).2 hj
    intro h
    exact S.p_unif.not_isUnit ((isUnit_map_iff (algebraMap W O) _).1 (by simpa using h))
  have hι : ∀ z : Qq, ι z ∈ Set.range (algebraMap O Kf) ↔ z ∈ Set.range (algebraMap W Qq) := by
    intro z
    refine ⟨fun h => ?_, ?_⟩
    · by_contra hz
      obtain ⟨o, ho⟩ := h
      have hz0 : z ≠ 0 := fun h0 => hz ⟨0, by rw [h0, map_zero]⟩
      obtain ⟨t, ht⟩ := (ValuationRing.isInteger_or_isInteger W z).resolve_left hz
      have htu : ¬ IsUnit t := by
        rintro ⟨u, rfl⟩
        apply hz
        refine ⟨(u⁻¹ : Wˣ), ?_⟩
        rw [← inv_inv z, ← ht]
        apply eq_inv_of_mul_eq_one_left
        rw [← map_mul, Units.inv_mul, map_one]
      have htm : t ∈ Ideal.span {(p : W)} := by
        rw [← S.p_unif.maximalIdeal_eq]
        exact htu
      obtain ⟨t', rfl⟩ := Ideal.mem_span_singleton'.1 htm
      have e1 : algebraMap O Kf (o * j (t' * p)) = 1 := by
        rw [map_mul, ho, ← S.ι_comp, ht, ← map_mul, mul_inv_cancel₀ hz0, map_one]
      have e2 : o * j (t' * p) = 1 := by
        apply IsFractionRing.injective O Kf
        rw [e1, map_one]
      apply hnu
      have : IsUnit (j (t' * p)) := IsUnit.of_mul_eq_one o (by rw [mul_comm]; exact e2)
      rw [map_mul, map_natCast] at this
      exact isUnit_of_mul_isUnit_right this
    · rintro ⟨t, rfl⟩
      exact ⟨j t, (S.ι_comp t).symm⟩
  rw [hι, hs]

theorem val_pos_iff {K : Type} [Field K] (val : AddValuation K (WithTop ℤ)) (z : K) :
    (0 : WithTop ℤ) < val z ↔ z = 0 ∨ ¬ (0 : WithTop ℤ) ≤ val z⁻¹ := by
  by_cases hz : z = 0
  · subst hz
    simp
  · simp only [hz, false_or, AddValuation.map_inv, not_le]
    obtain ⟨n, hn⟩ : ∃ n : ℤ, val z = n := WithTop.ne_top_iff_exists.1 (fun h => hz ((AddValuation.top_iff val).1 h)) |>.imp fun _ h => h.symm
    rw [hn, ← WithTop.LinearOrderedAddCommGroup.coe_neg]
    norm_cast
    omega

theorem mem_asIdeal_iff_inv {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] (v : HeightOneSpectrum R) (x : R) :
    x ∈ v.asIdeal ↔ x = 0 ∨ (algebraMap K (v.adicCompletion K) (algebraMap R K x))⁻¹ ∉ v.adicCompletionIntegers K := by
  by_cases hx : x = 0
  · subst hx
    simp
  · simp only [hx, false_or, HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, not_le]
    rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := K)]
    have h1 : (algebraMap K (v.adicCompletion K) (algebraMap R K x)) = ((algebraMap R K x : K) : v.adicCompletion K) := rfl
    rw [h1, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    have h0 : v.valuation K (algebraMap R K x) ≠ 0 := by
      simpa using hx
    rw [one_lt_inv₀ (zero_lt_iff.2 h0)]

theorem inv_int_iff {p : ℕ} {G : GAtP p} (v : Fin G.P.nV) (s : ℕ) {LL : Type} [Field LL]
    (val : AddValuation LL (WithTop ℤ)) (emb : LL →+* G.Kf)
    (hint : ∀ z, (0 : WithTop ℤ) ≤ val z ↔ emb z ∈ Set.range (algebraMap G.O G.Kf)) (z : LL) (y : G.P.Qq v)
    (hk : emb z = G.P.ι v ((G.P.σ v ^ s) y)) :
    y⁻¹ ∈ Set.range (algebraMap (G.P.W v) (G.P.Qq v)) ↔ (0 : WithTop ℤ) ≤ val z⁻¹ := by
  rw [hint, map_inv₀, hk, ← map_inv₀, ← map_inv₀]
  exact (iota_sigma_mem_range (G.P.setting v) s y⁻¹).symm

section Comparison₂

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V} {p : ℕ} {G : GAtP p}

theorem tie_mem_iff {L : ColLevel R F E sp gp C A clsLat} (t : Formalism.L2.Herm.GLevTie L G) (v : Fin G.P.nV) (x : 𝓞 F) :
    x ∈ (t.pl v).1.asIdeal ↔ x = 0 ∨
      ((t.eQ v _ rfl).symm ((t.spl _ (t.pl v).2 (inclE (F := F) ((t.pl v).1.adicCompletion F) (algebraMap F E (x : F)))).1))⁻¹ ∉
        Set.range (algebraMap (G.P.W v) (G.P.Qq v)) := by
  rw [t.spl_F, mem_asIdeal_iff_inv (K := F), t.completion_integers_iff v _ rfl, map_inv₀, RingEquiv.apply_symm_apply]

end Comparison₂

theorem int_map_eq_zero_iff {F E L : Type} [Field F] [Field E] [Field L] (g : F →+* E) (f : E →+* L)
    (x : 𝓞 F) : f (g (x : F)) = 0 ↔ x = 0 := by
  rw [map_eq_zero_iff f f.injective, map_eq_zero_iff g g.injective]
  exact RingOfIntegers.coe_eq_zero_iff



theorem place_of_tie : ∀ (D : D7) (sc : Scale) (Ce : ℝ)
    (Lc : ∀ u, ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
    (I : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
      LocId (Lc u) (D.what₂.places.resChar w) (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))
        (WQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w)))
        (QQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w))))
    (ψ : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
      Formalism.L2.Herm.awayFrom₂ (Lc u) (D.what₂.places.resChar w) →* (ORec D w (nFr D (D.what₂.places.resChar w)))ˣ)
    (hd : ∀ u w h, ((packC D Lc I ψ u w h).gat (rSc sc D.R.k (D.what₂.places.resChar w))
      (epSc D.R sc Ce (D.what₂.places.resChar w))).d = Module.finrank ℂ (D.mem u).A.Mu0)
    (H0 : Formalism.L2.Herm.Herm0 (recC D sc Ce Lc I ψ hd)) (hL : ∀ u, H0.lev0 u = Lc u)
    (B : GL (Fin D.R.k) D.host.E) (hBs : Cmp.StdB (recC D sc Ce Lc I ψ hd) B)
    (hB : ∀ u w hg (w' : HeightOneSpectrum (𝓞 D.host.F)) (h : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal),
      (I u w hg).fr w' h = bc (((RingHom.fst _ _).comp ((I u w hg).spl w' h).toRingHom).comp
        (inclE (F := D.host.F) (w'.adicCompletion D.host.F))) B)
    (iK : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
      KfRec D w (nFr D (D.what₂.places.resChar w)) →+* ℂ_[D.what₂.places.resChar w])
    (lam : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
      (algebraicClosure ℚ ℂ) →+* ℂ_[D.what₂.places.resChar w])
    (hK : ∀ u w hg (z : D.what₂.LL), iK u w hg (embRec D w (nFr D (D.what₂.places.resChar w)) z) =
      lamV (lam u w hg) (D.what₂.embLL z))
    (hPos : ∀ u w hg, (packC D Lc I ψ u w hg).posOK (iK u w hg) (lam u w hg))
    (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    (v : Fin (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))) (s : Fin (nFr D (D.what₂.places.resChar w)))
    (x : 𝓞 D.host.F),
    x ∈ (((hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL).g u w hg).pl v).1.asIdeal ↔
      (0 : WithTop ℤ) < D.what₂.places.val w (tauLL (recC D sc Ce Lc I ψ hd) ((gatTiesC D sc Ce Lc I ψ hd).gat_pos u w hg ⟨v, s⟩)
        (algebraMap D.host.F D.host.E (x : D.host.F))) := by
  intro D sc Ce Lc I ψ hd H0 hL B hBs hB iK lam hK hPos u w hg v s x
  have hpos := pos_C D sc Ce Lc I ψ hd H0 hL B hBs hB iK lam hK hPos u w hg v s
    (algebraMap D.host.F D.host.E (x : D.host.F))
  have hsig : sigD (recC D sc Ce Lc I ψ hd) (algebraMap D.host.F D.host.E (x : D.host.F)) =
      algebraMap D.host.F D.host.E (x : D.host.F) := AlgHom.commutes _ _
  have key : (cmpInC D sc Ce Lc I ψ hd H0 hL B hBs hB).embW u w hg
      (tauLL (recC D sc Ce Lc I ψ hd) ((gatTiesC D sc Ce Lc I ψ hd).gat_pos u w hg ⟨v, s⟩)
        (algebraMap D.host.F D.host.E (x : D.host.F))) =
      ((recC D sc Ce Lc I ψ hd).gat u w hg).P.ι v
        ((((recC D sc Ce Lc I ψ hd).gat u w hg).P.σ v ^ s.val)
          ((Cmp.locAt (hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL) u w hg B).iw v (algebraMap D.host.F D.host.E (x : D.host.F)))) := by
    have e : tauLL (recC D sc Ce Lc I ψ hd) ((gatTiesC D sc Ce Lc I ψ hd).gat_pos u w hg ⟨v, s⟩)
        (algebraMap D.host.F D.host.E (x : D.host.F)) = Cmp.tEL (recC D sc Ce Lc I ψ hd)
          ((gatTiesC D sc Ce Lc I ψ hd).gat_pos u w hg ⟨v, s⟩) (if Even s.val then algebraMap D.host.F D.host.E (x : D.host.F)
            else sigD (recC D sc Ce Lc I ψ hd) (algebraMap D.host.F D.host.E (x : D.host.F))) := by
      by_cases he : Even s.val
      · simp only [he, if_true, ite_true, ↓reduceIte]; rfl
      · simp only [he, if_false, ite_false, ↓reduceIte, hsig]; rfl
    rw [e]
    exact hpos
  refine (tie_mem_iff ((hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL).g u w hg) v x).trans ?_
  have hz : x = 0 ↔ tauLL (recC D sc Ce Lc I ψ hd) ((gatTiesC D sc Ce Lc I ψ hd).gat_pos u w hg ⟨v, s⟩)
      (algebraMap D.host.F D.host.E (x : D.host.F)) = 0 := by
    exact (int_map_eq_zero_iff (algebraMap D.host.F D.host.E) (Cmp.tEL (recC D sc Ce Lc I ψ hd) ((gatTiesC D sc Ce Lc I ψ hd).gat_pos u w hg ⟨v, s⟩)) x).symm
  refine Iff.trans ?_ (val_pos_iff (D.what₂.places.val w) (tauLL (recC D sc Ce Lc I ψ hd) ((gatTiesC D sc Ce Lc I ψ hd).gat_pos u w hg ⟨v, s⟩)
      (algebraMap D.host.F D.host.E (x : D.host.F)))).symm
  exact or_congr hz (not_congr (inv_int_iff v s.val (D.what₂.places.val w) ((cmpInC D sc Ce Lc I ψ hd H0 hL B hBs hB).embW u w hg)
    ((cmpInC D sc Ce Lc I ψ hd H0 hL B hBs hB).embW_int u w hg) _ _ key))

end GlobalTheory.TiePlace
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalIdentificationPlaceEqInducedRealPlaceStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G NumberField IsDedekindDomain Formalism.UG Formalism.L2.Forms
attribute [local instance] Formalism.BasicNotions.factResChar Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.mem_localPlace_asIdeal_iff_val_pos : ∀ (D : D7) (sc : Scale) (Ce : ℝ)
    (Lc : ∀ u, ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
    (I : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
      LocId (Lc u) (D.what₂.places.resChar w) (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))
        (WQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w)))
        (QQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w))))
    (ψ : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
      Formalism.L2.Herm.awayFrom₂ (Lc u) (D.what₂.places.resChar w) →* (ORec D w (nFr D (D.what₂.places.resChar w)))ˣ)
    (hd : ∀ u w h, ((packC D Lc I ψ u w h).gat (rSc sc D.R.k (D.what₂.places.resChar w))
      (epSc D.R sc Ce (D.what₂.places.resChar w))).d = Module.finrank ℂ (D.mem u).A.Mu0)
    (H0 : Formalism.L2.Herm.Herm0 (recC D sc Ce Lc I ψ hd)) (hL : ∀ u, H0.lev0 u = Lc u)
    (B : GL (Fin D.R.k) D.host.E) (hBs : Cmp.StdB (recC D sc Ce Lc I ψ hd) B)
    (hB : ∀ u w hg (w' : HeightOneSpectrum (𝓞 D.host.F)) (h : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal),
      (I u w hg).fr w' h = bc (((RingHom.fst _ _).comp ((I u w hg).spl w' h).toRingHom).comp
        (inclE (F := D.host.F) (w'.adicCompletion D.host.F))) B)
    (iK : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
      KfRec D w (nFr D (D.what₂.places.resChar w)) →+* ℂ_[D.what₂.places.resChar w])
    (lam : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
      (algebraicClosure ℚ ℂ) →+* ℂ_[D.what₂.places.resChar w])
    (hK : ∀ u w hg (z : D.what₂.LL), iK u w hg (embRec D w (nFr D (D.what₂.places.resChar w)) z) =
      lamV (lam u w hg) (D.what₂.embLL z))
    (hPos : ∀ u w hg, (packC D Lc I ψ u w hg).posOK (iK u w hg) (lam u w hg))
    (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    (v : Fin (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))) (s : Fin (nFr D (D.what₂.places.resChar w)))
    (x : 𝓞 D.host.F),
    x ∈ (((hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL).g u w hg).pl v).1.asIdeal ↔
      (0 : WithTop ℤ) < D.what₂.places.val w (tauLL (recC D sc Ce Lc I ψ hd) ((gatTiesC D sc Ce Lc I ψ hd).gat_pos u w hg ⟨v, s⟩)
        (algebraMap D.host.F D.host.E (x : D.host.F))) := by
  first | exact @GlobalTheory.TiePlace.place_of_tie | exact GlobalTheory.TiePlace.place_of_tie | (intros; apply GlobalTheory.TiePlace.place_of_tie <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsRecGOfIsLocalFamily

section

@[expose] public section

noncomputable section

namespace GlobalTheory.Mem.Top.Bl.TrueLocal

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G NumberField IsDedekindDomain Formalism.UG Formalism.L2.Forms GlobalTheory.Mem.LocalPack GlobalTheory.Mem.ConcreteRecord

attribute [local instance] Formalism.BasicNotions.factResChar Formalism.BasicNotions.Host.cmStar

def IsLocalFamily (sc : Scale) (D : D7) (L0 : LevelData D) (T : ∀ u : D.what₂.Word, Forms0 D u)
    (g : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) → GAtP (D.what₂.places.resChar w)) : Prop :=
  ∃ (I : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
      LocId (L0 u) (D.what₂.places.resChar w) (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))
        (WQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w)))
        (QQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w))))
    (ψ : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
      Formalism.L2.Herm.awayFrom₂ (L0 u) (D.what₂.places.resChar w) →* (ORec D w (nFr D (D.what₂.places.resChar w)))ˣ)
    (B : GL (Fin D.R.k) D.host.E)
    (iK : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
      KfRec D w (nFr D (D.what₂.places.resChar w)) →+* ℂ_[D.what₂.places.resChar w])
    (lam : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
      (algebraicClosure ℚ ℂ) →+* ℂ_[D.what₂.places.resChar w]),
    Cmp.StdB D B ∧
    (∀ u w hg (w' : HeightOneSpectrum (𝓞 D.host.F)) (h : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal),
      (I u w hg).fr w' h = bc (((RingHom.fst _ _).comp ((I u w hg).spl w' h).toRingHom).comp
        (inclE (F := D.host.F) (w'.adicCompletion D.host.F))) B) ∧
    (∀ u w hg (z : D.what₂.LL), iK u w hg (embRec D w (nFr D (D.what₂.places.resChar w)) z) =
      lamV (lam u w hg) (D.what₂.embLL z)) ∧
    (∀ u w hg, (packC D (fun u => L0 u) I ψ u w hg).posOK (iK u w hg) (lam u w hg)) ∧
    (∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
      PsiTied (LL := D.what₂.LL) (O := ORec D w (nFr D (D.what₂.places.resChar w)))
        (Kf := KfRec D w (nFr D (D.what₂.places.resChar w)))
        ((T u).cls0).lev (L0 u) (D.what₂.places.resChar w) (rank_eq_first_level D.R) D.what₂.embLL
        (embRec D w (nFr D (D.what₂.places.resChar w))) (ψ u w hg)) ∧
    g = gatOf D L0 I ψ sc



theorem exists_isLocalFamily (sc : Scale) {D : D7} {L0 : LevelData D} (T : ∀ u : D.what₂.Word, Forms0 D u)
    (hS : Formalism.L2.Herm.StdTied D) (hC : Companion D L0) (hJ : ∀ u, Joint0 L0 u (T u)) (hψ : ∀ u, LevelZeroCharacterRational T u) :
    ∃ g, (∀ u w h, (g u w h).d = Module.finrank ℂ (D.mem u).A.Mu0) ∧ IsLocalFamily sc D L0 T g :=
  let I := placeId D L0 hS hC
  have hAway := GlobalTheory.Mem.AwayChar.exists_psi D L0 T hJ hψ
  let ψ := fun u w hg => Classical.choose (hAway u w hg)
  have hTied := fun u w hg => Classical.choose_spec (hAway u w hg)
  let g := gatOf D L0 I ψ sc
  have hd := gatOf_d D L0 T hJ I ψ sc
  have h : IsLocalFamily sc D L0 T g :=
    ⟨I, ψ, stdBasis D hS, embK D L0, embAlg D L0, stdBasis_std D hS, fun _ _ _ _ _ => rfl,
      embK_embAlg D L0, posOK_placeId (D := D) (L0 := L0) hS hC ψ, hTied, rfl⟩
  ⟨g, hd, h⟩



theorem isRecG_of_isLocalFamily {sc : Scale} {D : D7} {L0 : LevelData D} {T : ∀ u : D.what₂.Word, Forms0 D u}
    (hJ : ∀ u, Joint0 L0 u (T u)) (hψ : ∀ u, LevelZeroCharacterRational T u) {g} (hd : ∀ u w h, (g u w h).d = Module.finrank ℂ (D.mem u).A.Mu0)
    (h : IsLocalFamily sc D L0 T g) :
    ∃ (Gt : GatTies (setGat D g hd)) (c : LatCmp (setGat D g hd)) (G : GroupCompatibilityAll (setGat D g hd) Gt c),
      IsRecG sc (setGat D g hd) Gt c G.herm G.forms ∧ (∀ u, G.herm.lev0 u = L0 u) ∧ (∀ u, G.forms u = forms0Set D g hd (T u)) ∧
      ∀ u w hg (v : Fin ((setGat D g hd).gat u w hg).P.nV) (s : Fin (((setGat D g hd).gat u w hg).P.n' v)) (x : 𝓞 D.host.F),
        x ∈ ((G.herm.g u w hg).pl v).1.asIdeal ↔
          (0 : WithTop ℤ) < D.what₂.places.val w (tauLL (setGat D g hd) (Gt.gat_pos u w hg ⟨v, s⟩)
            (algebraMap D.host.F D.host.E (x : D.host.F))) := by
  obtain ⟨I, ψ, B, iK, lam, hBs, hB, hK, hPos, hψ', rfl⟩ := h
  exact
    let buildRec := recC D sc 1 L0 I
    -- Infer the character type from `recC` to reuse its unit instances in the constructions below.
    let ψ := (fun {A : Type} {B : A → Type 1} (_ : ∀ a, B a) (a : A) => a) buildRec ψ
    let D' := buildRec ψ hd
    let H0 : Formalism.L2.Herm.Herm0 D' := ⟨L0, levTieG D sc 1 L0 (packC D L0 I ψ) hd⟩
    have hL : ∀ u, H0.lev0 u = L0 u := fun _ => rfl
    let T' : ∀ u, Forms0 D' u := fun u => forms0Set D D'.gat D'.gat_d (T u)
    let Gt := gatTiesC D sc 1 L0 I ψ hd
    let cmp := cmpInC D sc 1 L0 I ψ hd H0 hL B hBs hB
    have CH := Test.comparison_statements D sc L0 I ψ hd H0 hL T' B hBs hB iK lam hK hPos hJ hψ hψ'
    have hpos := pos_C D sc 1 L0 I ψ hd H0 hL B hBs hB iK lam hK hPos
    have hcmp := (CH.toHyp0 hpos).toHyp
    let c := Cmp.latCmpC T' Gt cmp hcmp
    let G : GroupCompatibilityAll D' Gt c :=
      groupCompatibilityOfRecursion D sc 1 L0 I ψ hd H0 hL T' B hBs hB hcmp
        (fun u w hg => isHyperbolicAt_rec_of_placeIdentification D u w hg (I u w hg))
    have hRec : IsRecG sc D' Gt c H0 T' :=
      IsRecG.intro D L0 I ψ hd H0 hL T' B hBs hB iK lam hK hPos CH rfl
    have hRetie : IsRecG sc D' Gt c G.herm G.forms :=
      LayerTwoModel.isRecG_retie hRec G.herm.g
    have hPlace := GlobalTheory.T.mem_localPlace_asIdeal_iff_val_pos
      D sc 1 L0 I ψ hd H0 hL B hBs hB iK lam hK hPos
    ⟨Gt, c, G, hRetie, fun _ => rfl, fun _ => rfl, hPlace⟩

end GlobalTheory.Mem.Top.Bl.TrueLocal

end
end
end
