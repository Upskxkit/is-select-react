import React, {memo, ReactElement, SyntheticEvent} from "react";
import PropTypes from "prop-types";
import "./SelectButton.scss"
// import { ReactComponent as DownIcon } from "../../svg/down.svg";
import {ReactComponent as DownIcon} from "../../svg/down.svg";
import Typography from "@material-ui/core/Typography";
import {SelectButtonInput} from "../../interface";

const SelectButton = ({handleClick, pending, className, value, placeholder, type, opened, hasError}: SelectButtonInput): ReactElement => {
  const checkPendingHandler = (event: SyntheticEvent): void => {
    if (pending) {
      return;
    }
    handleClick(event);
  };

  return (
    <div
      className={`${className ? className : ""} 
      selectButton ${opened ? "opened" : ""} 
      ${pending ? "loading" : type} 
      ${hasError ? "error" : ""}`}
      onClick={checkPendingHandler}>
      <div>
        <Typography
          component="div"
          noWrap
          variant="subtitle2"
          color="primary">
          {!value ? placeholder : value}
        </Typography>
      </div>
      <div className="indicatorContainer">
        <DownIcon className={`${opened ? "opened" : ""}`}/>
      </div>
    </div>
  );
};

SelectButton.propTypes = {
  handleClick: PropTypes.func,
  pending: PropTypes.bool,
  opened: PropTypes.bool,
  className: PropTypes.string,
  value: PropTypes.string,
  placeholder: PropTypes.string,
  type: PropTypes.string
};

export default memo(SelectButton);
