# Security queries

This repository is a place to store and share customized security queries and libraries. This contains queries in [LGTM blog posts](https://lgtm.com/blog), but also project specific libraries. If you find it useful and would like to share some cool queries that you wrote for finding vulnerabilities in open source projects with us, or if you would like to help us to improve the project-specific QL libraries, please feel free to contribute and create a PR!

These queries should be used with the free [QL for Eclipse plugin](https://help.semmle.com/ql-for-eclipse/Content/WebHelp/home-page.html). To run these queries on an open source project that is available on [LGTM](https://lgtm.com), follow the first two steps in [Basic Usage](https://help.semmle.com/ql-for-eclipse/Content/WebHelp/basic-usage.html) to obtain and import the project snapshot, then go to the specific `.ql` file in this repository that contains the query, [import the parent project into Eclipse](https://help.semmle.com/ql-for-eclipse/Content/WebHelp/import-ql-project.html), open and select the file and press `Ctrl+R`. There are also some links to snapshots for specific versions of certain projects in the `README` files in this repository.

## Using the Path Explorer

Many queries in this repository makes use of the Taint-Tracking library in QL, which allows you to visualize the code path that goes from a tainted source to a dangerous sink. To enable this, click `Window` on the Eclipse menu bar, then click `Show View > Other... > Semmle > Path Explorer` to display the Path Explorer window. This will show you the tainted path when you click on a query result.

