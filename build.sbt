enablePlugins(ScalaJSPlugin)

name := "fragger"
organization := "hz.ricardo"
version := "0.2"
scalaVersion := "2.13.2"

// This is an application with a main method
scalaJSUseMainModuleInitializer := true

libraryDependencies ++= Seq(
  "org.scala-js" %%% "scalajs-dom" % "1.0.0",
  "com.lihaoyi" %%% "scalatags" % "0.9.1",
  "org.scala-lang.modules" %%% "scala-parser-combinators" % "1.1.2",
  "hz.ricardo" %%% "graph-rewriting" % "0.3"
)

// Add support for the DOM in `run` and `test`
jsEnv := new org.scalajs.jsenv.jsdomnodejs.JSDOMNodeJSEnv()
