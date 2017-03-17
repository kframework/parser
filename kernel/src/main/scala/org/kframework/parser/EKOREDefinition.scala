package org.kframework.parser

import org.apache.commons.lang3.StringEscapeUtils

import org.kframework.minikore.interfaces.pattern._
import org.kframework.minikore.interfaces.build.Builders

import org.kframework.minikore.converters.KoreToMini._
import org.kframework.minikore.implementation.MiniKore.{Definition, Module, Sentence, Import, SortDeclaration, SymbolDeclaration, Attributes, Rule, Axiom}


case class ParserNormalization(b: Builders) {

  val meta = org.kframework.minikore.MiniKoreMeta(b)
  val patternUtils = org.kframework.minikore.MiniKorePatternUtils(b)
  val outerUtils = org.kframework.minikore.MiniKoreOuterUtils(b)
  val dsl = KDefinitionDSL(b)

  import b._
  import meta._
  import patternUtils._
  import outerUtils._
  import dsl._

  // Utilities
  // =========

  def stripString(front: Int, back: Int): String => String = (str: String) => StringEscapeUtils.unescapeJava(str drop front dropRight back)

  def removeSubNodes(label: String): Pattern => Pattern = {
    case Application(name, args) => Application(name, args filterNot { case Application(Symbol(`label`), _) => true case _ => false })
    case pattern                 => pattern
  }

  // Normalization passes
  // ====================

  val removeParseInfo: Pattern => Pattern = {
    case Application(Symbol("#"), Application(Symbol("#"), actual :: _) :: _) => actual
    case pattern                                              => pattern
  }

  val normalizeTokens: Pattern => Pattern = {
    //case dv@DomainValue("KSymbol@KTOKENS", _)     => upDomainValue(dv)
    //case DomainValue(name@"KString@KTOKENS", str) => upDomainValue(DomainValue(name, stripString(1, 1)(str)))
    //case DomainValue("KMLPattern@KML", name)      => Application("KMLApplication", Seq(upSymbol(name)))
    case pattern                                  => pattern
  }

  // Disagreements on encoding
  // =========================

  val toKoreEncodingProdItems: Pattern => Pattern = {
    case DomainValue(`KTerminal`, str)        => Application(iTerminal, Seq(S(str)))
    case DomainValue(`KRegexTerminal`, regex) => Application(iRegexTerminal, Seq(S(regex)))
    case DomainValue(`KNonTerminal`, str)     => Application(iNonTerminal, Seq(S(str)))
  }

  val toKoreEncodingAttributes: Pattern => Pattern = {
    case Application(`iMainModule`, Seq(DomainValue(`KValue`, modName)))   => Application(iMainModule, Seq(S(modName)))
    case Application(`iEntryModules`, Seq(DomainValue(`KValue`, modName))) => Application(iEntryModules, Seq(S(modName)))
    case Application(`KSyntaxPriority`, Seq(ksp))                          => Application(iSyntaxPriority, flattenBySymbols(Symbol("KPriorityItems"), Symbol(".KPriorityItems"))(ksp))
    case Application(`KProduction`, args)                                  => Application(Symbol("production"), args map toKoreEncodingProdItems)
    case pattern                                                           => pattern
  }

  val toKoreEncodingSentences: Sentence => Sentence = {
    case Import(name, atts)                         => Import(name, atts map toKoreEncodingAttributes)
    case SortDeclaration(sort, atts)                => SortDeclaration(sort, atts map toKoreEncodingAttributes)
    case SymbolDeclaration(sort, label, args, atts) => SymbolDeclaration(sort, label, args, atts map toKoreEncodingAttributes)
    case Rule(pattern, atts)                        => Rule(pattern, atts map toKoreEncodingAttributes)
    case Axiom(pattern, atts)                       => Axiom(pattern, atts map toKoreEncodingAttributes)
  }

  val toKoreEncodingMod: Module => Module = {
    case Module(name, sentences, atts) =>
      val koreEncodingAttributes = atts map toKoreEncodingAttributes
      val priorityDummyAxioms = getAttributeKey(iSyntaxPriority, koreEncodingAttributes) map (kp => dummySentence(Seq(Application(iSyntaxPriority, kp map (kpg => Application(iSyntaxPriorityGroup, flattenBySymbols(Symbol("KSymbolList"), Symbol(".KSymbolList"))(kpg)))))))
      Module(name, (sentences ++ priorityDummyAxioms) map toKoreEncodingSentences, koreEncodingAttributes)
  }

  val toKoreEncodingDef: Definition => Definition = {
    case Definition(modules, atts) => Definition(modules map toKoreEncodingMod, atts map toKoreEncodingAttributes)
  }

  // Preprocessing
  // =============

  val preProcess: Pattern => Pattern = traverseTopDown(removeParseInfo) andThen traverseBottomUp(normalizeTokens)
}

case class EKOREDefinition(b: Builders) {

  val meta = org.kframework.minikore.MiniKoreMeta(b)
  val dsl = KDefinitionDSL(b)
  val koreDef = KOREDefinition(b)
  val parserNorm = ParserNormalization(b)

  import org.kframework.minikore.converters.KoreToMini.{iMainModule, iEntryModules}
  import org.kframework.minikore.implementation.MiniKore.Module
  import b._
  import meta._
  import dsl._
  import koreDef._
  import parserNorm._

  // K-PRETTY-PRODUCTION
  // ===================

  val KTerminal                 = Sort("KTerminal")
  val KRegexTerminal            = Sort("KRegexTerminal")
  val KNonTerminal              = Sort("KNonTerminal")
  val KProduction               = Sort("KProduction")
  val KProductions              = Sort("KProductions")
  val KProductionsBlock         = Sort("KProductionsBlock")
  val KPriority                 = Sort("KPriority")
  val KProductionWithAttributes = Sort("KProductionWithAttributes")

  val K_PRETTY_PRODUCTION: Module = module("K-PRETTY-PRODUCTION",
    imports("KDEFINITION"),

    syntax(KTerminal)      is Regex(KRegexString) att "token",
    syntax(KRegexTerminal) is Regex("r" + KRegexString) att "token",
    syntax(KNonTerminal)   is Regex(KRegexSymbol) att "token",

    syntax(KProduction) is KTerminal,
    syntax(KProduction) is KRegexTerminal,
    syntax(KProduction) is KNonTerminal,
    syntax(KProduction) is (KProduction, KProduction) att(klabel("KProduction"), "assoc"),
    syntax(KProductionWithAttributes) is (KProduction, KAttributes) att klabel("KProductionWithAttributes"),

    syntax(KProductionsBlock) is KProductionWithAttributes,
    syntax(KProductionsBlock) is (KProductionWithAttributes, "|", KProductionsBlock) att klabel("KProductionsBlock"),

    syntax(KProductions) is KProductionsBlock,
    syntax(KProductions) is (KProductionsBlock, ">", KProductions) att(klabel("KProductionsPriority"), "assoc"),

    syntax(KPriority) is "" att klabel(".KPriorityItems"),
    syntax(KPriority) is KSymbolList,
    syntax(KPriority) is (KPriority, ">", KPriority) att(klabel("KPriorityItems"), "assoc"),

    syntax(KSentence) is ("syntax", KSymbol, KAttributes) att klabel("KSortDeclaration"),
    syntax(KSentence) is ("syntax", KSymbol, "::=", KProductions) att klabel("KSyntaxProduction"),
    syntax(KSentence) is ("syntax", "priority", KPriority) att klabel("KSyntaxPriority")
  )

  // TODO: correctly process precede/follow regex clauses
  val normalizeProductionItems: Pattern => Pattern = {
    case DomainValue(name@"KTerminal@K-PRETTY-PRODUCTION", term)       => application(name, stripString(1, 1)(term))
    case DomainValue(name@"KRegexTerminal@K-PRETTY-PRODUCTION", rterm) => Application(name, Seq(Application("#", Nil), Application(stripString(2, 1)(rterm), Nil), Application("#", Nil)))
    case DomainValue(name@"KNonTerminal@K-PRETTY-PRODUCTION", nterm)   => application(name, nterm)
    case pattern                                                       => pattern
  }

  val desugarPrettySentence: Pattern => Seq[Pattern] = {

    case Application("KSyntaxProduction", sort :: Application("KProductionWithAttributes", production :: atts :: Nil) :: Nil) =>
      val downedAtts = downAttributes(atts)
      val prodItems  = flattenByLabels("KProduction")(traverseBottomUp(normalizeProductionItems)(production))
      val newKLabel  = upSymbol(getKLabel(downedAtts).getOrElse(prodItems map makeCtorString mkString))
      val args       = prodItems collect { case Application("KNonTerminal@K-PRETTY-PRODUCTION", Application(nt, Nil) :: Nil) => upSymbol(nt) }
      Seq(Application("KSymbolDeclaration", Seq(sort, newKLabel, consListLeftSubsort("KSymbolList", ".KSymbolList")(args), upAttributes(downedAtts :+ prod(prodItems)))))

    case Application("KSyntaxProduction", sort :: (kpb@Application("KProductionsBlock", _)) :: Nil) =>
      val sents        = flattenByLabels("KProductionsBlock")(kpb) flatMap (kp => desugarPrettySentence(Application("KSyntaxProduction", Seq(sort, kp))))
      val klabels      = sents collect { case Application("KSymbolDeclaration", _ :: klabel :: _ :: _ :: Nil) => klabel }
      val prioritySent = Application("KSyntaxPriority", Seq(consListLeftSubsort("KSymbolList", ".KSymbolList")(klabels)))
      sents :+ prioritySent

    case Application("KSyntaxProduction", sort :: (kpp@Application("KProductionsPriority", _)) :: Nil) =>
      val kpbs                 = flattenByLabels("KProductionsPriority")(kpp) flatMap (kpb => desugarPrettySentence(Application("KSyntaxProduction", Seq(sort, Application("KProductionsBlock", Seq(kpb))))))
      val (pBlocks, prodSents) = kpbs partition { case Application("KSyntaxPriority", _) => true case _ => false }
      val prioritySent         = Application("KSyntaxPriority", Seq(consListLeftSubsort("KPriorityItems", ".KPriorityItems")(pBlocks map { case Application("KSyntaxPriority", pBlock :: Nil) => pBlock })))
      prodSents :+ prioritySent

    case pattern => Seq(pattern)
  }

  val desugarPrettyModule: Pattern => Pattern = {

    case Application("KModule", name :: sentences :: atts :: Nil) =>
      val desugaredSentences         = flattenByLabels("KSentenceList", ".KSentenceList")(sentences) flatMap desugarPrettySentence
      val (priorities, newSentences) = desugaredSentences partition { case Application("KSyntaxPriority", _) => true case _ => false }
      Application("KModule", Seq(name, consListLeft("KSentenceList", ".KSentenceList")(newSentences), upAttributes(downAttributes(atts) ++ priorities)))

    case pattern => pattern
  }

  // K-CONCRETE-RULES
  // ================

  val KBubbleRegex = "[^ \n\r\t]+"

  val KBubbleItem = Sort("KBubbleItem")
  val KBubble = Sort("KBubble")

  val K_CONCRETE_RULES: Module = module("K-CONCRETE-RULES",
    imports("KML"),

    syntax(KBubbleItem) is Regex(KBubbleRegex) att("avoid", "token", application("reject2", "rule|syntax|endmodule|configuration|context")),

    syntax(KBubble) is (KBubble, KBubbleItem) att(klabel("KBubble"), "avoid"),
    syntax(KBubble) is KBubbleItem att "avoid",

    syntax(KMLPattern) is KBubble
  )

  def mkRuleParserDefinition(astDef: Pattern): Definition = {
    val defn = downDefinition(traverseTopDown(removeSubNodes("KRule"))(astDef))
    val mainModuleName = getAttributeKey(iMainModule, defn.att) match { case Seq(Seq(Application(name, Nil))) => name }
    val sorts = allSorts(defn) toSeq
    val newSentences = sorts flatMap (sort => Seq(syntax(Sort(sort)) is KMLVariable, syntax(KMLPattern) is Sort(sort))) map (_.att())
    val ruleParserModuleName = mainModuleName + "-RULE-PARSER"
    val ruleParserModule = Module(ruleParserModuleName, imports(mainModuleName) +: imports("KML") +: newSentences, Seq.empty)
    val ruleParserAtts = updateAttribute(iMainModule, Application(ruleParserModuleName, Nil)) andThen updateAttribute(iEntryModules, Application(ruleParserModuleName, Nil))
    Definition(defn.modules :+ ruleParserModule :+ KML :+ KTOKENS, ruleParserAtts(defn.att))
  }

  def mkParser(d: Definition): String => Pattern = input => {
    import org.kframework.parser.concrete2kore.ParseInModule
    import org.kframework.attributes.Source
    import org.kframework.kore.ADT.SortLookup
    import org.kframework.minikore.MiniToKore
    import org.kframework.minikore.KoreToMini

    val parser = new ParseInModule(MiniToKore(toKoreEncodingDef(d)).mainModule)
    parser.parseString(input, SortLookup("KMLPattern"), Source(""))._1 match {
      case Right(x) => KoreToMini(x)
      case Left(y) => throw new Error("runParser error: " + y.toString)
    }
  }

  def resolveBubbles(parser: String => Pattern): Pattern => Pattern = {
    case b@Application("KBubble", _) => preProcess(parser(flattenByLabels("KBubble")(b) map { case DomainValue("KBubbleItem@K-CONCRETE-RULES", str) => str } mkString " "))
    case pattern                     => pattern
  }

  val upUserPattern: Pattern => Pattern = {
    case sym@Application("KMLDomainValue", _)                                      => sym
    case Application(label, args) if (KTOKENS_LABELS ++ KML_LABELS) contains label => Application(label, args map upUserPattern)
    case Application(label, args)                                                  => Application("KMLApplication", Seq(upSymbol(label), consListLeft("KMLPatternList", ".KMLPatternList")(args map upUserPattern)))
  }

  def resolveRule(parser: String => Pattern): Pattern => Pattern = {
    case Application("KRule", rule :: atts :: Nil) => Application("KRule", Seq(upUserPattern(traverseTopDown(resolveBubbles(parser))(rule)), atts))
    case pattern                                   => pattern
  }

  def resolveDefinitionRules(parsed: Pattern): Pattern = traverseTopDown(resolveRule(mkParser(mkRuleParserDefinition(parsed))))(parsed)

  // EKORE
  // =====

  val EKORE_MODULE: Module = module("EKORE",
    imports("K-PRETTY-PRODUCTION"),
    imports("K-CONCRETE-RULES")
  )

  val EKORE = definition((KORE.modules :+ K_PRETTY_PRODUCTION :+ K_CONCRETE_RULES :+ EKORE_MODULE):_*) att(application(iMainModule, "EKORE"), application(iEntryModules, "EKORE"))

  val ekoreToKore: Pattern => Pattern = traverseTopDown(desugarPrettyModule)
}
