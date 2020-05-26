package hz.ricardo
package fragger

import scala.collection.mutable
import scala.scalajs.js
import js.annotation.JSGlobal
import org.scalajs.dom
import dom.html
import dom.experimental.URLSearchParams
import scalatags.JsDom.all._
import scala.util.parsing.combinator._
import graph_rewriting._
import moments._

object Fragger {

  type N = String
  type E = IdDiEdge[Int,N]
  type L = String
  val Graph = MarkedDiGraph.withType[N,L,E,L]
  type Graph = MarkedDiGraph[N,L,E,L]
  implicit val graphBuilder = MarkedDiGraph.empty[N,L,E,L] _


  // -- Parsing --

  object GraphParser extends Parsers with RegexParsers {

    lazy val ident: Parser[String] =
      """\w+""".r | failure("an identifier was expected")

    def addNode(g: Graph, name: N, label: Option[L], mark: Int) = {
      g += name
      if (label.isDefined)
        g(name).label = label.get
      mark match {
        case 0 => ()
        case 1 => g(name).inMark
        case 2 => g(name).outMark
        case 3 => g(name).mark
      }
    }

    lazy val graph: Parser[Graph] =
      // rep((node <~ ";") | (edge <~ ";")) ^^ {
      repsep(edge | node | failure("a node or an edge was expected"),
        ";" | ",") <~ opt(";" |
          failure("'->' or ',' or ';' was expected")) ^^ {
        nodesAndEdges =>
        val g = Graph()()
        var i = 0
        for (nodeOrEdge <- nodesAndEdges) nodeOrEdge match {
          case Node(name, label, mark) =>
            addNode(g, name, label, mark)
          case Edge(source,target,label) => {
            addNode(g, source.name, source.label, source.mark)
            addNode(g, target.name, target.label, target.mark)
            val e = IdDiEdge(i, source.name, target.name)
            i += 1
            g += e
            if (label.isDefined)
              g(e).label = label.get
          }
        }
        g
      }

    lazy val node: Parser[Node] =
      markedNode | inMarkedNode | outMarkedNode | unmarkedNode

    lazy val unmarkedNode: Parser[Node] = ident ~ label ^^ {
      case name ~ label => Node(name, label, 0) }

    lazy val inMarkedNode: Parser[Node] = (">" ~> ident <~ "<") ~ label ^^ {
      case name ~ label => Node(name, label, 1) }

    lazy val outMarkedNode: Parser[Node] = ("<" ~> ident <~ ">") ~ label ^^ {
      case name ~ label => Node(name, label, 2) }

    lazy val markedNode: Parser[Node] = ("|" ~> ident <~ "|") ~ label ^^ {
      case name ~ label => Node(name, label, 3) }

    lazy val edge: Parser[Edge] = node ~ arrow ~ node ^^ {
      case source ~ label ~ target => Edge(source, target, label) }

    lazy val arrow: Parser[Option[L]] =
      ("->" ~> label) | failure("'->' or ';' was expected")

    lazy val label: Parser[Option[L]] = opt("[" ~> ident <~ "]")

    sealed abstract class NodeOrEdge
    case class Node(name: N, label: Option[L], mark: Int)
        extends NodeOrEdge
    case class Edge(source: Node, target: Node, label: Option[L])
        extends NodeOrEdge

    def parse(s: String, errorDiv: html.Div, pos: String): Graph =
      parse(super[Parsers].phrase(graph), s) match {
        case Success(g, _) => g
        case NoSuccess(msg, next) => {
          errorDiv.appendChild(div(cls:="alert alert-danger")(
            s"Error parsing $pos: " + msg.replace("`", "'") + " " +
              (if (next.pos.column <= 1)
                 "at the beginning of expression"
               else
                 s"after '${s.substring(0,next.pos.column-1)}'.")
          ).render)
          throw new IllegalArgumentException(
            s"string '$s' couldn't be parsed as a graph")
        }
      }
  }


  // -- Naming observables --

  class ObsNaming(obs: Seq[(String, Graph)], start: Int = 0)
      extends GraphNaming[N,L,E,L,MarkedDiGraph] {

    val cnt = utils.Counter(start)
    val index = mutable.Map[Graph, Int]()
    val isos = mutable.Map[Graph, Graph]()

    def apply(g: Graph): String =
      obs.find(_._2 iso g) match {
        case Some((name, _)) => name
        case None =>
          if (index contains g) s"F${index(g)}"
          else if (isos contains g) s"F${index(isos(g))}"
          else index find { case (h, _) => g iso h } match {
            case Some((h, _)) => { isos(g) = h; s"F${index(h)}" }
            case None => { val i = cnt.next; index(g) = i; s"F$i" }
          }
      }

    def seq: Seq[(Graph, String)] = obs.map(_.swap) ++ (
      for ((g, i) <- index.toSeq.sortBy(_._2))
      yield (toIntNodes(g), s"F$i"))

    def toIntNodes(g: Graph): Graph = {
      val nodes = g.nodes.zipWithIndex.toMap.mapValues(_.toString)
      val edges = (for (e <- g.edges) yield
        (e, IdDiEdge(e.id, nodes(e.source), nodes(e.target)))).toMap
      val h = Graph(nodes.values, edges.values)
      for (n <- g.inMarks) h(nodes(n)).inMark
      for (n <- g.outMarks) h(nodes(n)).outMark
      for ((n, l) <- g.nodelabels) h(nodes(n)).label = l
      for ((e, l) <- g.edgelabels) h(edges(e)).label = l
      h
    }
  }

  // -- Observable counter --

  val cnt = utils.Counter()
  def countFrags = (g: Graph) => { cnt.next; None }


  // -- Rules, Observables and Invariants --

  case class RuleInput(name: html.Input, lhs: html.Input, rhs: html.Input)
  case class ObsInput(name: html.Input, graph: html.Input)
  case class InvInput(search: html.Input, replace: html.Input)

  val rules = mutable.ArrayBuffer.empty[RuleInput]
  val obs = mutable.ArrayBuffer.empty[ObsInput]
  val inv = mutable.ArrayBuffer.empty[InvInput]

  def newRule: html.Div = {
    val name = input(tpe:="text", width:="100%").render
    val lhs = input(tpe:="text", width:="100%").render
    val rhs = input(tpe:="text", width:="100%").render
    rules += RuleInput(name, lhs, rhs)
    div(cls:="row", margin:=10)(
      div(cls:="col-md-5")(lhs),
      div(cls:="col-md-1 glyphicon glyphicon-arrow-right",
        aria.hidden:=true, style:="line-height: 35px"),
      div(cls:="col-md-5")(rhs),
      div(cls:="col-md-1")(name)).render
  }

  def newObs: html.Div = {
    val name = input(tpe:="text", width:="100%").render
    val graph = input(tpe:="text", width:="100%").render
    obs += ObsInput(name, graph)
    div(cls:="row", margin:=10)(
      div(cls:="col-md-2")(name),
      div(cls:="col-md-10")(graph)).render
  }

  def newInv: html.Div = {
    val search = input(tpe:="text", width:="100%").render
    val replace = input(tpe:="text", width:="100%").render
    inv += InvInput(search, replace)
    div(cls:="row", margin:=10)(
      div(cls:="col-md-6")(search),
      div(cls:="col-md-1 glyphicon glyphicon-arrow-right",
        aria.hidden:=true, style:="line-height: 35px"),
      div(cls:="col-md-5")(replace)).render
  }

  val ruleDiv: html.Div = div().render
  val obsDiv: html.Div = div().render
  val invDiv: html.Div = div().render
  val addRule = () => ruleDiv.appendChild(newRule)
  val addObs = () => obsDiv.appendChild(newObs)
  val addInv = () => invDiv.appendChild(newInv)
  val removeRule = () => {
    if (rules.length > 1) {
      ruleDiv.removeChild(ruleDiv.lastChild)
      rules.trimEnd(1)
    }
  }
  val removeObs = () => {
    if (obs.length > 1) {
      obsDiv.removeChild(obsDiv.lastChild)
      obs.trimEnd(1)
    }
  }
  val removeInv = () => {
    if (inv.length > 1) {
      invDiv.removeChild(invDiv.lastChild)
      inv.trimEnd(1)
    }
  }

  val defaultMaxNumEqs: String = "10"
  val maxNumEqs: html.Input =
    input(tpe:="text", size:=1, value:=defaultMaxNumEqs).render
  val errorDiv: html.Div = div().render
  val resultDiv: html.Div = div().render
  val rateEqs: html.Input =
    input(tpe:="checkbox", cls:="form-check-input",
      id:="rateEqs").render

  def isEmptyRule(name: String, lhs: String, rhs: String): Boolean =
    name == "" && lhs == "" && rhs == ""

  def isValidRule(name: String, lhs: String, rhs: String): Boolean =
    name != "" &&
    !name.contains('"') && !lhs.contains('"') && !rhs.contains('"')

  def validateRule(name: String, lhs: String, rhs: String) =
    if (name == "") {
      errorDiv.appendChild(div(cls:="alert alert-danger")(
        "Rules must have a non-empty rate.").render)
    } else if (name.contains('"') ||
                lhs.contains('"') ||
                rhs.contains('"')) {
      errorDiv.appendChild(div(cls:="alert alert-danger")(
        s"""Rule with rate '${name}' contains quotes (").""" +
          " This is not allowed.").render)
    }

  def parseRule(name: String, lhs: String, rhs: String)
      : Rule[N,L,E,L,MarkedDiGraph] = Rule(
    GraphParser.parse(lhs, errorDiv,
      s"the left-hand side of rule with rate '${name}'"),
    GraphParser.parse(rhs, errorDiv,
      s"the right-hand side of rule with rate '${name}'"),
    Rate(name))


  def isEmptyObs(name: String, obs: String): Boolean =
    name == "" && obs == ""

  def isValidObs(name: String, obs: String): Boolean =
    name != "" && obs != ""

  def validateObs(name: String, obs: String) =
    if (name == "" || obs == "") {
      errorDiv.appendChild(div(cls:="alert alert-danger")(
        "Observables must have a non-empty name" +
        " and graph expression.").render)
    } else if (name.contains('"') ||
                obs.contains('"')) {
      errorDiv.appendChild(div(cls:="alert alert-danger")(
        s"""Observable '${name}' contains quotes (").""" +
          " This is not allowed.").render)
    }

  def parseObs(name: String, obs: String): (String, Graph) =
    (name, GraphParser.parse(obs, errorDiv, s"observable '${name}'"))


  def isEmptyInv(search: String, replace: String): Boolean =
    search == "" && replace == ""

  def validateInv(search: String, replace: String) =
    if (search == "") {
      errorDiv.appendChild(div(cls:="alert alert-danger")(
        "Invariants must have a non-empty observable to be replaced."
      ).render)
    } else if (search.contains('"')) {
      errorDiv.appendChild(div(cls:="alert alert-danger")(
        s"""Invariant '${search}' contains quotes (").""" +
          " This is not allowed.").render)
    } else if (replace.contains('"')) {
      errorDiv.appendChild(div(cls:="alert alert-danger")(
        s"""Invariant '${replace}' contains quotes (").""" +
          " This is not allowed.").render)
    }

  def parseInv(search: String, replace: String)
      : Graph => Option[Pn[N,L,E,L,MarkedDiGraph]] = {
    val sg = GraphParser.parse(search,
      errorDiv, s"invariant '${search}'")
    if (replace == "") {
      // Not sure if the following works.
      // I'm writing it by hand just in case.
      // cancelIfIso(Seq(
      //   GraphParser.parse(search,
      //     errorDiv, s"invariant '${search}'")))
      def invariant(g: Graph): Option[Pn[N,L,E,L,MarkedDiGraph]] =
        if (g.iso(sg)) Some(Pn.zero) else None
      invariant _
    } else {
      // This didn't work. Not sure why.
      // transformIfIso(Seq(
      //   GraphParser.parse(search,
      //     errorDiv, s"invariant '${search}'")),
      //   GraphParser.parse(replace,
      //     errorDiv, s"observable '${replace}'"))
      val rg = GraphParser.parse(replace,
        errorDiv, s"observable '${replace}'")
      def invariant(g: Graph): Option[Pn[N,L,E,L,MarkedDiGraph]] =
        if (g.iso(sg)) Some(Pn(Mn(rg))) else None
      invariant _
    }
  }


  // -- Generate equations --

  def toDot(g: Graph) =
    (for (n <- g.nodes) yield (
      if (g(n).inMarked && g(n).outMarked) "|" + n + "|"
      else if (g(n).inMarked) ">" + n + "<"
      else if (g(n).outMarked) "<" + n + ">"
      else n) + (g(n).label match {
        case Some(l) => "[" + l + "]"
        case None => ""
      })).mkString(", ") + (
      if (g.nodes.isEmpty || g.edges.isEmpty) "" else ", ") +
  (for (e <- g.edges.toSeq) yield
    s"${e.source}->${e.target}").mkString(", ")

  val genEquations = () => {
    errorDiv.innerHTML = ""
    val rs = for {
      RuleInput(name, lhs, rhs) <- rules
      if !isEmptyRule(name.value, lhs.value, rhs.value)
    } yield {
      validateRule(name.value, lhs.value, rhs.value)
      parseRule(name.value, lhs.value, rhs.value)
    }
    val os = for {
      ObsInput(name, graph) <- obs
      if !isEmptyObs(name.value, graph.value)
    } yield {
      validateObs(name.value, graph.value)
      parseObs(name.value, graph.value)
    }
    val is = for {
      InvInput(search, replace) <- inv
      if !isEmptyInv(search.value, replace.value)
    } yield {
      validateInv(search.value, replace.value)
      parseInv(search.value, replace.value)
    }
    if (rs.length == 0)
      errorDiv.appendChild(div(cls:="alert alert-danger")(
        "No rules were given so no differential equations" +
          " can be computed.").render)
    if (os.length == 0)
      errorDiv.appendChild(div(cls:="alert alert-danger")(
        "No observables were given so no differential equations" +
          " can be computed.").render)
    if (errorDiv.innerHTML != "")
      throw new IllegalArgumentException()

    val mne = maxNumEqs.value.toInt
    val is0 = countFrags +: (if (rateEqs.checked)
      Seq(splitConnectedComponents[N,L,E,L,MarkedDiGraph] _) else Nil)
    val odes =
      generateMeanODEs[N,L,E,L,MarkedDiGraph](
        mne, rs, os.map(_._2).toSeq, (is0 ++ is):_*)

    // FIXME: better output
    val printer = ODEPrinter(odes)
    val naming = new ObsNaming(os.toSeq)
    val lines = for (ODE(lhs, rhs) <- printer.simplify) yield (
      s"d(${naming(lhs)})/dt = " + (if (rhs.isEmpty) "0" else
        rhs.terms.map(printer.strMn(_, naming)).mkString(" + ")))
    val names = for ((g, n) <- naming.seq)
                yield s"$n := ${toDot(g)}"
    if (names.length > lines.size) {
      errorDiv.appendChild(div(cls:="alert alert-warning")(
        s"The number of observables obtained is ${names.length}. ",
        s"The number of ODEs computed is ${lines.size}. ",
        "Hence, the system of ODEs is not closed. ",
        "There are more ODEs to compute but the maximum number of ",
        s"ODEs is set to ${mne}. ",
        "Increase the maximum number of ODEs if you wish to compute ",
        "ODEs for more observables.").render)
    }
    resultDiv.innerHTML = ""
    resultDiv.appendChild(
      div(cls:="row", margin:=10)(h2("Results")).render)
    val ta = textarea(style:="margin-bottom: 50px; width: 100%; " +
      "height: auto; font-family: monospace;")(
      names.mkString("\n") + "\n\n" + lines.mkString("\n")).render
    resultDiv.appendChild(ta)
    ta.style.height = (ta.scrollHeight + 5) + "px"
  }


  // -- Info and syntax boxes --

  def seemore(base: html.Div, extra: html.Div): html.Div = {
    var isExpanded = false
    val seemoreAnchor: html.Anchor =
      a(cls:="text-muted small")("see more").render
    seemoreAnchor.onclick = (e: dom.MouseEvent) => {
      if (isExpanded) {
        extra.style.display = "none"
        base.style.paddingBottom = "30px"
        seemoreAnchor.textContent = "see more"
      } else {
        extra.style.display = "block"
        base.style.paddingBottom = "40px"
        seemoreAnchor.textContent = "see less"
      }
      isExpanded = !isExpanded
    }
    div(position.absolute, bottom:="10px", right:="30px")(
      seemoreAnchor).render
  }

  val info: html.Div = div(cls:="col-md-5 bg-success text-left",
    style:="border: 2px solid #000; border-radius: 20px;" +
      " padding-top: 20px; padding-bottom: 30px;" +
      " padding-left: 30px; padding-right: 30px;")(
    p("This ", a(href:="https://www.scala-js.org/")(
      "Scala.js"), " ", a(href:="https://github.com/rhz/fragger")(
      "web app"), " generates systems of differential equations",
      " that describe the average behaviour of graph observables.",
      " For more information check the following papers.")).render

  val extraInfo = div(display.none)(
    ul(cls:="list-unstyled")(
      li(a(href:="http://link.springer.com/" +
        "chapter/10.1007/978-3-319-11737-9_1")(
        "\"Approximations for Stochastic" +
          " Graph Rewriting\" (ICFEM 2014)")),
      li(a(href:="http://link.springer.com/" +
        "chapter/10.1007/978-3-319-20860-2_1")(
        "\"Moment Semantics for Reversible" +
          " Rule-Based Systems\" (RC 2015)")),
      li("\"Computing approximations for graph" +
        " transformation systems\" (MeMo 2015)")),
    p("All of them can be read at ",
      a(href:="https://tardis.ed.ac.uk/~rhz/")(
        "https://tardis.ed.ac.uk/~rhz/"),
      ". The computations are performed by the ",
      a(href:="https://github.com/rhz/graph-rewriting")(
        "graph-rewriting"), " library.")).render

  info.appendChild(seemore(info, extraInfo))
  info.appendChild(extraInfo)

  val syntax: html.Div = div(
    cls:="col-md-6 col-md-offset-1 bg-info text-left",
    style:="border: 2px solid #000; border-radius: 20px;" +
      " padding-bottom: 30px;" +
      " padding-left: 30px; padding-right: 30px;")(
    h3(cls:="text-center")("Syntax"),
    p(code("graph := ((node | edge)(\";\" | \",\"))*")),
    p(code("edge := node ->([label])? node")),
    p(code("node := name([label])?")),
    p("Examples: ",
      a(href:=dom.window.location.pathname +
        "?re=1&m=bunnies")("bunnies"), ", ",
      a(href:=dom.window.location.pathname +
        "?mne=2&m=bimotor")("bimotor"), ", ",
      a(href:=dom.window.location.pathname +
        "?re=1&m=pa")("preferential attachment"), ", ",
      a(href:=dom.window.location.pathname +
        "?re=1&m=irreversible")("irreversible marks"), ", ",
      a(href:=dom.window.location.pathname +
        "?re=1&m=koch")("Koch snowflake"), ", ",
      a(href:=dom.window.location.pathname +
        "?re=1&m=voter")("voter model"), ".")).render

  val extraSyntax: html.Div = div(display.none)(
    p("Here ", code("->"), ", ", code("["),
      ", and ", code("]"), " are literals."),
    p("Names and labels can be any word."),
    p("The left- and right-hand sides expect graphs."),
    p("Names should be unique on each graph",
      " and are used to map the left-hand side (lhs)",
      " into the right-hand side (rhs)."),
    p("The node name may be surrounded by 3 types of marks",
      " like ", code("|name|"), " or ", code("<name>"),
      " or ", code(">name<"), ", where ", code ("|"), ", ",
      code("<"), ", and ", code(">"), " are literals. ",
      code("|name|"), " matches nodes with same degree, ",
      code("<name>"), " matches nodes with same out-degree,",
      " and ", code(">name<"), " matches nodes with same",
      " in-degree.")).render

  syntax.appendChild(seemore(syntax, extraSyntax))
  syntax.appendChild(extraSyntax)


  // -- Compress model --

  // assumes it is a valid rule (non-empty, no quotes)
  def squishRule(name: String, lhs: String, rhs: String)
      : String = '"' + name.replaceAll("\\s", "") + "\",\"" +
    lhs.replaceAll("\\s", "") +  "\",\"" +
    rhs.replaceAll("\\s", "") +  "\""

  // assumes it is a valid observable (non-empty, no quotes)
  def squishObs(name: String, graph: String)
      : String = '"' + name.replaceAll("\\s", "") + "\",\"" +
    graph.replaceAll("\\s", "") +  "\""

  // assumes it is a valid invariant (non-empty, no quotes)
  def squishInv(search: String, replace: String)
      : String = "i\"" + search.replaceAll("\\s", "") + "\",\"" +
    replace.replaceAll("\\s", "") +  "\""

  @js.native
  @JSGlobal("LZString")
  object LZString extends js.Object {
    def compressToEncodedURIComponent(x: String): String = js.native
    def decompressFromEncodedURIComponent(x: String): String = js.native
  }

  def compressRules: String = {
    val squished = for (RuleInput(name, lhs, rhs) <- rules
      if !isEmptyRule(name.value, lhs.value, rhs.value)) yield {
      validateRule(name.value, lhs.value, rhs.value)
      squishRule(name.value, lhs.value, rhs.value)
    }
    if (errorDiv.innerHTML != "")
      throw new IllegalArgumentException()
    // dom.window.btoa(squished.mkString("."))
    LZString.compressToEncodedURIComponent(squished.mkString("."))
  }

  def compressModel: String = {
    val squishedRules = for (RuleInput(name, lhs, rhs) <- rules
      if !isEmptyRule(name.value, lhs.value, rhs.value)) yield {
      validateRule(name.value, lhs.value, rhs.value)
      squishRule(name.value, lhs.value, rhs.value)
    }
    val squishedObs = for (ObsInput(name, graph) <- obs
      if !isEmptyObs(name.value, graph.value)) yield {
      validateObs(name.value, graph.value)
      squishObs(name.value, graph.value)
    }
    val squishedInv = for (InvInput(search, replace) <- inv
      if !isEmptyInv(search.value, replace.value)) yield {
      validateInv(search.value, replace.value)
      squishInv(search.value, replace.value)
    }
    if (errorDiv.innerHTML != "")
      throw new IllegalArgumentException()
    LZString.compressToEncodedURIComponent(
      (squishedRules ++ squishedObs ++ squishedInv).mkString("."))
  }


  // -- Share model --

  def shareParams: String = {
    val params = new URLSearchParams()
    if (maxNumEqs.value != defaultMaxNumEqs)
      params.append("mne", maxNumEqs.value)
    if (rateEqs.checked)
      params.append("re", "1")
    params.append("m", compressModel)
    params.toString
  }

  val sharePopup: html.Div = div(cls:="bg-info text-left",
    style:="border: 2px solid #000; border-radius: 5px;" +
      " padding-bottom: 0px; padding-top: 10px;" +
      " padding-left: 15px; padding-right: 15px;",
    display.none, position.absolute, bottom:="60px", right:="40px",
    width:="34.5vw")().render

  def copyToClipboard(x: String) =
    () => {
      val nav = dom.window.navigator.asInstanceOf[js.Dynamic]
      nav.clipboard.writeText(x)
      // val urlInput = dom.document.getElementById(...)
      // urlInput.focus
      // urlInput.select
      // dom.document.execCommand("copy")
    }

  var popupHidden = true
  val shareModel = () => {
    errorDiv.innerHTML = ""
    if (popupHidden) {
      val url = dom.window.location.pathname + "?" + shareParams
      sharePopup.appendChild(
        div("Use the following URL to link directly to this model",
          div(cls:="input-group", borderRadius:="5px",
            marginBottom:="15px", marginTop:="5px")(
            input(tpe:="text", cls:="form-control",
              width:="100%", value:=url),
            span(cls:="input-group-btn")(
              button(cls:="btn btn-default " +
                "glyphicon glyphicon-copy",
                onclick:=copyToClipboard(url))))).render)
      sharePopup.style.display = "block"
    } else {
      sharePopup.removeChild(sharePopup.firstChild)
      sharePopup.style.display = "none"
    }
    popupHidden = !popupHidden
  }


  // -- HTML --

  val mainDiv: html.Div =
    div(cls:="container text-center",id:="main-div")(
      // -- Title --
      div(cls:="row", margin:=20)(
        div(cls:="col-md-4 col-md-offset-4")(
          h1("Fragger")),
        div(cls:="col-md-4")(
          img(src:="ms.svg", cls:="pull-rigth",
            width:="20vw", height:="5rem"))),
      div(cls:="row", margin:=10, marginTop:=50)(info, syntax),
      // -- Rules --
      div(cls:="row", margin:=10)(
        div(cls:="col-md-4 col-md-offset-4")(
          h2("Rules")),
        div(cls:="col-md-1")(
          button(cls:="btn btn-default glyphicon glyphicon-plus",
            marginTop:="15px", marginBottom:="10px",
            onclick:=addRule)()),
        div(cls:="col-md-1")(
          button(cls:="btn btn-default glyphicon glyphicon-minus",
            marginTop:="15px", marginBottom:="10px",
            onclick:=removeRule)())),
      div(cls:="row", margin:=10)(
        div(cls:="col-md-5")("left-hand side"),
        div(cls:="col-md-1"),
        div(cls:="col-md-5")("right-hand side"),
        div(cls:="col-md-1")("rate")),
      ruleDiv,
      // -- Observables --
      div(cls:="row", margin:=10)(
        div(cls:="col-md-4 col-md-offset-4")(
          h2("Observables")),
        div(cls:="col-md-1")(
          button(cls:="btn btn-default glyphicon glyphicon-plus",
            marginTop:="15px", marginBottom:="10px",
            onclick:=addObs)()),
        div(cls:="col-md-1")(
          button(cls:="btn btn-default glyphicon glyphicon-minus",
            marginTop:="15px", marginBottom:="10px",
            onclick:=removeObs)())),
      div(cls:="row", margin:=10)(
        div(cls:="col-md-2")("name"),
        div(cls:="col-md-10")("graph expression")),
      obsDiv,
      // -- Invariants --
      div(cls:="row", margin:=10)(
        div(cls:="col-md-4 col-md-offset-4")(
          h2("Invariants")),
        div(cls:="col-md-1")(
          button(cls:="btn btn-default glyphicon glyphicon-plus",
            marginTop:="15px", marginBottom:="10px",
            onclick:=addInv)()),
        div(cls:="col-md-1")(
          button(cls:="btn btn-default glyphicon glyphicon-minus",
            marginTop:="15px", marginBottom:="10px",
            onclick:=removeInv)())),
      div(cls:="row", margin:=10)(
        div(cls:="col-md-6")("observable to be replaced"),
        div(cls:="col-md-1"),
        div(cls:="col-md-5")("replacement")),
      invDiv,
      // -- Errors --
      errorDiv,
      // -- Buttons --
      div(cls:="row", margin:="10px",
        marginTop:="50px", marginBottom:="20px")(
        div(cls:="col-md-6", marginTop:="7px")(
          "Maximum number of ODEs: ", maxNumEqs),
        div(cls:="col-md-4")(
          button(cls:="btn btn-lg btn-primary", width:="100%",
            onclick:=genEquations)("Generate equations!")),
        div(cls:="col-md-2")(
          button(cls:="btn btn-lg btn-default pull-right",
            onclick:=shareModel)("Share model"),
          sharePopup)),
      div(cls:="row", // margin:=10,
        style:="margin-bottom: 50px")(
        div(cls:="col-md-6 form-check",
          title:="Assume independence between connected components")(
          rateEqs, label(cls:="form-check-label",
            style:="font-weight: normal; padding-left: 10px;",
            `for`:="rateEqs")("Rate equations"))),
      // -- Results --
      resultDiv).render


  // -- Decompress model --

  def getModelString(v: String) =
    if (v == "bunnies")
      """"a","1,2","1->3,2->3"."S","1->3,2->3,1->4,2->4"."""
    else if (v == "bimotor") {
      val g0 = "b[b],c[c],b->c,b->c"
      val g1 = "b[b],c1[c],c2[c],c1->c2,b->c1,b->c1"
      val g2 = "b[b],c1[c],c2[c],c1->c2,b->c1,b->c2"
      val g3 = "b[b],c1[c],c2[c],c1->c2,b->c2,b->c2"
      s""""kFE","$g1","$g2"."kBC","$g2","$g1".""" +
      s""""kFC","$g2","$g3"."kBE","$g3","$g2".""" +
      s""""G0","$g0"."G2","$g2".""" +
      s"""i"$g1","$g0".i"$g3","$g0".""" +
      s"""i"$g1,b->c1","".""" +
      s"""i"$g1,b->c2","".""" +
      s"""i"$g2,b->c2","".""" +
      s"""i"$g3,b->c2","".""" +
      s"""i"$g2,c1->c2,b->c1","".""" +
      s"""i"$g2,c2->c1,b->c2","".""" +
      s"""i"$g1,c3[c],c2->c3,b->c3","".""" +
      s"""i"$g1,c3[c],c3->c2,b->c3","".""" +
      s"""i"$g1,c1->c2,b->c1","".""" +
      s"""i"$g1,c1->c2","".""" +
      s"""i"$g1,c2->c1,b->c1","".""" +
      s"""i"$g1,c2->c1","".""" +
      s"""i"$g2,c3[c],c1->c3,b->c3","".""" +
      s"""i"$g2,c3[c],c2->c3,b->c3","".""" +
      s"""i"$g2,c3[c],c3->c2,b->c3","".""" +
      s"""i"$g2,c1->c2,b->c2","".""" +
      s"""i"$g2,c1->c2","".""" +
      s"""i"$g2,c2->c1","".""" +
      s"""i"$g3,c3[c],c1->c3,b->c3","".""" +
      s"""i"$g3,c3[c],c3->c1,b->c3","".""" +
      s"""i"$g3,c1->c2,b->c2","".""" +
      s"""i"$g3,c1->c2",""."""
    } else if (v == "pa" || v == "irreversible" || v == "koch" ||
      v == "voter") {
      errorDiv.appendChild(
        div(cls:="alert alert-danger")(
          "Model '" + v + "' has not been implemented yet.").render)
      throw new IllegalArgumentException()
    } else
      LZString.decompressFromEncodedURIComponent(v) + "."

  def addSpace(x: String): String =
    x.replaceAll(",", ", ").replaceAll(";", "; ")

  def decompressModel(v: String): Unit = {
    val triple = """"([^"]*)","([^"]*)","([^"]*)"\.""".r
    // val twople = """(?<!,)"([^"]*)","([^"]*)"\.""".r
    val twople = """"([^"]*)","([^"]*)"\.""".r
    val invre = """i"([^"]*)","([^"]*)"\.""".r
    //  p = js.URIUtils.decodeURIComponent(v)
    val p = getModelString(v)
    for (m <- triple.findAllMatchIn(p)) {
      ruleDiv.appendChild(newRule)
      val RuleInput(name, lhs, rhs) = rules.last
      name.value = m.group(1)
      lhs.value = addSpace(m.group(2))
      rhs.value = addSpace(m.group(3))
    }
    val q = triple.replaceAllIn(p, "")
    for (m <- invre.findAllMatchIn(q)) {
      invDiv.appendChild(newInv)
      val InvInput(search, replace) = inv.last
      search.value = addSpace(m.group(1))
      replace.value = addSpace(m.group(2))
    }
    val r = invre.replaceAllIn(q, "")
    for (m <- twople.findAllMatchIn(r)) {
      obsDiv.appendChild(newObs)
      val ObsInput(name, graph) = obs.last
      name.value = m.group(1)
      graph.value = addSpace(m.group(2))
    }
  }


  // -- Main: parse query string and load interface --

  def main(args: Array[String]): Unit = {
    dom.document.body.appendChild(mainDiv)
    val urlParams = new URLSearchParams(
      dom.window.location.search)
    // for (js.Tuple2(k, v) <- urlParams.entries()) {
    urlParams.forEach { (v, k) =>
      if (k == "mne")
        maxNumEqs.value = v
      else if (k == "re" && v != "0")
        rateEqs.click
      else if (k == "m") {
        decompressModel(v)
      }
    }
    // initial number of rules and observables
    // if none given via url search params
    val n = 2
    if (rules.isEmpty)
      for (i <- 1 to n)
        ruleDiv.appendChild(newRule)
    if (obs.isEmpty)
      for (i <- 1 to n)
        obsDiv.appendChild(newObs)
    if (inv.isEmpty)
      invDiv.appendChild(newInv)
    // TODO: update url search params as model changes
    // https://developers.google.com/web/updates/2016/01/urlsearchparams?hl=en
  }
}
