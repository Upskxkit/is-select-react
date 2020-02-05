import React, { ReactElement } from "react";
import "./SelectMenu.scss";
import { SingleMenu } from "../../interface";
declare function SelectSingle({ cancelHandler, applyHandler, items, open }: SingleMenu): ReactElement;
declare namespace SelectSingle {
    var propTypes: object;
}
declare const _default: React.MemoExoticComponent<typeof SelectSingle>;
export default _default;
