module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.TaylorWilesObstructionBound
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ChebotarevFamilies.ChebOne
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
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PairedDualFirstOrderDualMatrixSpace
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ChebotarevFamilies.FrSNormal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ChebotarevFamilies.HomBound
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ChebotarevFamilies.PLNormal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ChebotarevFamilies.PhiDec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ChebotarevFamilies.PhiGS
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ChebotarevFamilies.StarSingle
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ChebotarevFamilies.ChebFam

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.chebFam :
    ∀ (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (U : Subgroup (G L Ω)) (q : ℕ) (g : Fin q → G L Ω) (A : Set (Plc (Lp L))), IsOpen (U : Set (G L Ω)) → A.Finite → ∃ (v : Fin q → Plc (Lp L)) (w : Fin q → Plc L) (B : Fin q → ValuationSubring Ω) (σ : Fin q → G L Ω), Function.Injective v ∧ ∀ j, v j ∉ A ∧ IsPlaceOver (B j) (w j) ∧ IsPlaceOver (B j) (v j) ∧ Dec (F := Lp L) (B j) ≤ (resP L Ω).range ∧ IsFrob (F := L) (B j) (normV (w j)) (σ j) ∧ σ j * (g j)⁻¹ ∈ U := by
  intro L Ω _ _ _ _ _ _ U q g A hU hA
  revert g
  induction q with
  | zero =>
    intro g
    exact ⟨Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun j => j.elim0⟩
  | succ q ih =>
    intro g
    obtain ⟨v, w, B, σ, hinj, hj⟩ := ih (fun i => g i.castSucc)
    obtain ⟨v0, w0, B0, σ0, h1, h2, h3, h4, h5, h6⟩ :=
      chebOne L Ω U (g (Fin.last q)) (A ∪ Set.range v) hU (hA.union (Set.finite_range v))
    refine ⟨fun i => Fin.lastCases v0 v i, fun i => Fin.lastCases w0 w i,
      fun i => Fin.lastCases B0 B i, fun i => Fin.lastCases σ0 σ i, ?_, ?_⟩
    · intro i j hij
      induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
        simp only [Fin.lastCases_last, Fin.lastCases_castSucc] at hij
      · rfl
      · exact (h1 (Or.inr ⟨_, hij.symm⟩)).elim
      · exact (h1 (Or.inr ⟨_, hij⟩)).elim
      · rw [hinj hij]
    · intro j
      induction j using Fin.lastCases with
      | last =>
        simp only [Fin.lastCases_last]
        exact ⟨fun h => h1 (Or.inl h), h2, h3, h4, h5, h6⟩
      | cast i =>
        simp only [Fin.lastCases_castSucc]
        exact hj i
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ChebotarevFamilies.LevUp

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.levUp :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (V0 : s.Lev) (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (n : ℕ) (r : Resid V0.frame O n) (Q : Set (Plc (Lp L))), Q.Finite → (∀ v ∈ Q, ∃ B : ValuationSubring Ω, IsPlaceOver B v ∧ Dec (F := Lp L) B ≤ (resP L Ω).range) → ∃ V : s.Lev, V.S' = V0.S' ∪ Q ∧ ∃ h : (globOf r V).Hom (globOf r V0), ∀ g, h.p (toGS Ω V.S' g) = toGS Ω V0.S' g := by
  intro l _ L Ω _ _ _ _ _ _ s V0 O _ _ _ n r Q hQ hQs
  have hsub : (⋃ v ∈ (V0.S' ∪ Q)ᶜ, ⋃ A ∈ {A : ValuationSubring Ω | IsPlaceOver A v}, Inertia (F := Lp L) A) ⊆
      ⋃ v ∈ V0.S'ᶜ, ⋃ A ∈ {A : ValuationSubring Ω | IsPlaceOver A v}, Inertia (F := Lp L) A :=
    Set.biUnion_subset_biUnion_left (Set.compl_subset_compl.mpr Set.subset_union_left)
  have hNS : NS Ω (V0.S' ∪ Q) ≤ NS Ω V0.S' :=
    Subgroup.topologicalClosure_minimal _
      ((Subgroup.normalClosure_mono hsub).trans (Subgroup.le_topologicalClosure _))
      (Subgroup.isClosed_topologicalClosure _)
  let π : GS Ω (V0.S' ∪ Q) →* GS Ω V0.S' :=
    QuotientGroup.map _ _ (MonoidHom.id _) (fun x hx => hNS hx)
  have hπ : ∀ g, π (toGS Ω (V0.S' ∪ Q) g) = toGS Ω V0.S' g := fun g => rfl
  have hπc : Continuous π := by
    refine (QuotientGroup.isQuotientMap_mk (NS Ω (V0.S' ∪ Q))).continuous_iff.mpr ?_
    exact continuous_toGS Ω V0.S'
  have hπs : Function.Surjective π := by
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (NS Ω V0.S') y
    exact ⟨toGS Ω (V0.S' ∪ Q) g, rfl⟩
  have hconj : ∀ σ h, h ∈ (resP L Ω).range → σ * h * σ⁻¹ ∈ (resP L Ω).range := by
    intro σ h hh
    rw [← V0.hη] at hh ⊢
    simp [hh]
  refine ⟨{ S' := V0.S' ∪ Q
            fin := V0.fin.union hQ
            sub := V0.sub.trans Set.subset_union_left
            split := ?_
            η := V0.η.comp π
            hη := fun g => by simpa only [MonoidHom.comp_apply, hπ] using V0.hη g
            η_open := V0.η_open.preimage hπc
            η_c := by simpa only [MonoidHom.comp_apply, hπ] using V0.η_c
            ε := V0.ε.comp π
            hε := by
              ext g : 1
              simpa only [MonoidHom.comp_apply, hπ] using DFunLike.congr_fun V0.hε g
            ε_cont := V0.ε_cont.comp hπc }, rfl, ?_⟩
  · intro v hv
    rcases hv with hv | hv
    · exact V0.split v hv
    · obtain ⟨B, hB, hdec⟩ := hQs v hv
      obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver hB (s.hA v)
      intro τ hτ
      have hτ' : σ⁻¹ * τ * σ ∈ Dec (F := Lp L) B := by
        open Pointwise in
        rw [mem_Dec, mul_smul, mul_smul, hσ, mem_Dec.mp hτ, ← hσ, inv_smul_smul]
      have := hconj σ _ (hdec hτ')
      simpa [mul_assoc] using this
  · exact ⟨⟨π, hπc, hπs, fun _ => rfl, rfl, fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩, fun _ => rfl⟩
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AutomorphicDetection.ArPl

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.arPl : ArPl := by
  intro hC l _ L Ω _ _ _ _ _ _ s V0 O _ _ _ hO _ n r hS
  haveI : CharP (ResidueField O) l := hO.char
  have hphi : PhiCond V0.frame.Γ l := phiGS hC.gf l L Ω s V0
  refine ⟨hphi, ?_⟩
  intro q sg hsg
  obtain ⟨H, hH⟩ := hEx l V0.frame O n r
  obtain ⟨W, hWH, hWlim⟩ := frat l V0.frame.Γ H hphi
  have hlift : ∀ x : V0.frame.G₀, ∃ g : G L Ω, V0.pr g = x := by
    intro x
    obtain ⟨g', hg'⟩ := QuotientGroup.mk'_surjective (NS Ω V0.S') (show GS Ω V0.S' from x.1)
    have hr : g' ∈ (resP L Ω).range := by
      rw [← V0.hη g']
      have e : (toGS Ω V0.S') g' = (show GS Ω V0.S' from x.1) := hg'
      rw [e]
      exact x.2
    obtain ⟨g, rfl⟩ := hr
    exact ⟨g, Subtype.ext hg'⟩
  choose g hg using fun j => hlift (sg j)
  let ρ : G L Ω →* V0.frame.Γ := V0.η.ker.subtype.comp V0.pr
  have hρc : Continuous ρ := (continuous_toGS Ω V0.S').comp continuous_resP
  let U : ℕ → Subgroup (G L Ω) := fun N =>
    ((W N).toOpenSubgroup : Subgroup V0.frame.Γ).comap ρ ⊓ (cycMod L Ω l N).ker
  have hUo : ∀ N, IsOpen (U N : Set (G L Ω)) := by
    intro N
    refine IsOpen.inter ((W N).toOpenSubgroup.isOpen.preimage hρc) ?_
    have h1 := (isOpen_discrete ({1} : Set (ZMod (l ^ N)))).preimage
      (GlobalTheory.TameQuot.continuous_cycMod (F := L) (Ω := Ω) l N)
    have e : ((cycMod L Ω l N).ker : Set (G L Ω)) =
        (fun x => ((cycMod L Ω l N x : (ZMod (l ^ N))ˣ) : ZMod (l ^ N))) ⁻¹' {1} := by
      ext x
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage, Set.mem_singleton_iff,
        Units.val_eq_one]
    change IsOpen ((cycMod L Ω l N).ker : Set (G L Ω))
    rw [e]
    exact h1
  have hSfin : s.S.Finite := hS ▸ V0.fin
  choose v w B σ hinj hP using fun N => chebFam L Ω (U N) q (fun j => (g j)⁻¹) s.S (hUo N) hSfin
  have hlw : ∀ N j, (l : 𝓞 L) ∉ (w N j).asIdeal := by
    intro N j hl
    apply (hP N j).1
    left
    rw [← (hP N j).2.2.1]
    rw [← (hP N j).2.1] at hl
    simpa using hl
  have hTQ := fun N j => hC.tame.1 L Ω l (B N j) (w N j) (hP N j).2.1 (hlw N j)
  choose τ hτ using fun N j => (hTQ N j).2.2.2.2.1
  choose VN hVS hN hNe using fun N => levUp l L Ω s V0 O n r (Set.range (v N)) (Set.finite_range _)
    (by rintro _ ⟨j, rfl⟩; exact ⟨B N j, (hP N j).2.2.1, (hP N j).2.2.2.1⟩)
  have hK := fun N => kerLe l L Ω s V0 (VN N) O n r (hN N) (H.toOpenSubgroup : Subgroup V0.frame.Γ)
    q (v N) (B N) (τ N) (hNe N) (hVS N)
    (fun j => ⟨by rw [hS]; exact (hP N j).1, (hP N j).2.2.1, (hP N j).2.2.2.1, hτ N j⟩)
  have hcg : ∀ j, cycZ L Ω l (g j) = 1 := by
    intro j
    have h1 : cycZ L Ω l (g j) = V0.ε (toGS Ω V0.S' (resP L Ω (g j))) := by
      rw [← MonoidHom.comp_apply, V0.hε]
      rfl
    rw [h1]
    have h2 := hsg j
    rw [← hg j] at h2
    exact h2
  have hNq : ∀ N j, normV (w N j) ≡ 1 [MOD l ^ N] := by
    intro N j
    have hu := (hP N j).2.2.2.2.2
    simp only [inv_inv] at hu
    have hk : cycMod L Ω l N (σ N j * g j) = 1 := (Subgroup.mem_inf.1 hu).2
    have hgm : cycMod L Ω l N (g j) = 1 := by simp [cycMod, hcg j]
    rw [map_mul, hgm, mul_one] at hk
    have hz := cycZ_toZModPow_eq (hlw N j) (hP N j).2.1 (hP N j).2.2.2.2.1.2 N
    have hk' : PadicInt.toZModPow N ((cycZ L Ω l (σ N j) : ℤ_[l])) = 1 := by
      have := congrArg Units.val hk
      simpa [cycMod] using this
    rw [hk', map_natCast] at hz
    rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_one]
    exact hz.symm
  have hWm : ∀ N j, (show V0.frame.Γ from (hN N).p ((VN N).pr (σ N j)⁻¹).1) * ((sg j).1)⁻¹ ∈ W N := by
    intro N j
    have e1 : (hN N).p ((VN N).pr (σ N j)⁻¹).1 = ρ (σ N j)⁻¹ := hNe N (resP L Ω (σ N j)⁻¹)
    have e2 : (sg j).1 = ρ (g j) := by
      rw [← hg j]
      rfl
    rw [e1, e2]
    have hu := (hP N j).2.2.2.2.2
    simp only [inv_inv] at hu
    have hm : ρ (σ N j * g j) ∈ W N := (Subgroup.mem_inf.1 hu).1
    have hc := (W N).isNormal'.conj_mem _ hm (ρ (g j))
    have hi := Subgroup.inv_mem _ hc
    have eq : ρ (σ N j)⁻¹ * (ρ (g j))⁻¹ = (ρ (g j) * ρ (σ N j * g j) * (ρ (g j))⁻¹)⁻¹ := by
      simp only [map_mul, map_inv]
      group
    rw [eq]
    exact hi
  have htame : ∀ N j, ((((VN N).pr (τ N j)) ^ normV (w N j))⁻¹ *
      (((VN N).pr (σ N j)⁻¹)⁻¹ * (VN N).pr (τ N j) * (VN N).pr (σ N j)⁻¹)).1 ∈
      PL l (Subgroup.comap (hN N).p (H.toOpenSubgroup : Subgroup V0.frame.Γ)) := by
    intro N j
    have hσD : σ N j ∈ Dec (B N j) := (hP N j).2.2.2.2.1.1
    have hτD : τ N j ∈ Dec (B N j) := Ine_le_Dec _ (hτ N j).1
    have ht := ((hTQ N j).2.2.2.2.2 ⟨σ N j, hσD⟩ ⟨τ N j, hτD⟩ (hP N j).2.2.2.2.1 (hτ N j)).2.1
    have hm := (hK N).2.1 j _ ht
    have e : (((VN N).pr (τ N j)) ^ normV (w N j))⁻¹ *
        (((VN N).pr (σ N j)⁻¹)⁻¹ * (VN N).pr (τ N j) * (VN N).pr (σ N j)⁻¹) =
        (VN N).pr (((⟨τ N j, hτD⟩ : Dec (B N j)) ^ normV (w N j))⁻¹ *
          ((⟨σ N j, hσD⟩ : Dec (B N j)) * ⟨τ N j, hτD⟩ * (⟨σ N j, hσD⟩ : Dec (B N j))⁻¹) : Dec (B N j)) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow, map_mul, map_inv, map_pow, inv_inv]
    rw [e]
    exact hm
  let T : TWGrp (globOf r V0) :=
    { q := q
      H := H
      H_η := fun x hx => by
        obtain ⟨h1, -, -⟩ := (hH x).1 hx
        exact h1
      H_ε := fun x hx => by
        obtain ⟨-, -, h3⟩ := (hH x).1 hx
        exact h3
      GN := fun N => globOf r (VN N)
      h := hN
      sg := sg
      sg_mem := hsg
      Nq := fun N j => normV (w N j)
      Nq_mod := hNq
      ph := fun N j => (VN N).pr (σ N j)⁻¹
      ta := fun N j => (VN N).pr (τ N j)
      ph_lim := fun V j hV => (hWlim V hV).mono fun N hle => hle (hWm N j)
      ph_H := fun N j => hWH N (hWm N j)
      ta_ker := fun N j => (hK N).1 j _ (hτ N j).1
      tame := htame
      ker_le := fun N => (hK N).2.2
      hb := Nat.card (HomL l (H.toOpenSubgroup : Subgroup V0.frame.Γ)) *
        l ^ (q * (H.toOpenSubgroup : Subgroup V0.frame.Γ).index)
      fin0 := hphi _ H.toOpenSubgroup.isOpen
      finN := fun N => homBound l (VN N).frame.Γ V0.frame.Γ (hN N).p H q (fun j => ((VN N).pr (τ N j)).1) (hN N).cont
        (hN N).surj (fun j => (hK N).1 j _ (hτ N j).1) ((hK N).2.2) (hphi _ H.toOpenSubgroup.isOpen)
      phiV := fun x => phiDec hC.lf l L Ω (s.A x.1) (s.w x.1) (s.hw x.1)
      phiU := fun u => phiDec hC.lf l L Ω (s.A u.1) (s.w u.1) (s.hw u.1) }
  refine ⟨T, ⟨{
      V := VN
      e := fun N =>
        { p := MonoidHom.id _
          cont := continuous_id
          surj := Function.surjective_id
          η := fun _ => rfl
          c := rfl
          ε := fun _ => rfl
          φ := fun _ _ => rfl
          φu := fun _ _ => rfl }
      e_inj := fun N => Function.injective_id
      e_h := fun N x => hNe N x
      v := v
      v_inj := hinj
      v_not := fun N j => (hP N j).1
      S_eq := fun N => by rw [hVS N, hS]
      w := w
      B := B
      B_w := fun N j => (hP N j).2.1
      B_v := fun N j => (hP N j).2.2.1
      split := fun N j => (hP N j).2.2.2.1
      Nq := fun N j => rfl
      fr := fun N j => (σ N j)⁻¹
      fr_dec := fun N j => inv_mem (hP N j).2.2.2.2.1.1
      fr_frob := fun N j => by simpa using (hP N j).2.2.2.2.1
      τ := τ
      τ_gen := hτ
      ph := fun N j => rfl
      ta := fun N j => rfl
      H_eq := hH }⟩, rfl, fun j => rfl⟩
end
end
